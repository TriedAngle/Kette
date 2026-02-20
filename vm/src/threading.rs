use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};
use std::thread::{self, JoinHandle, Thread};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

static NEXT_THREAD_TOKEN: AtomicU64 = AtomicU64::new(1);
static THREAD_REGISTRY: OnceLock<Mutex<HashMap<u64, Thread>>> = OnceLock::new();
static START_TIME: OnceLock<Instant> = OnceLock::new();

thread_local! {
    static THREAD_TOKEN: u64 = {
        let token = NEXT_THREAD_TOKEN.fetch_add(1, Ordering::Relaxed);
        register_thread(token, thread::current());
        token
    };
}

fn registry() -> &'static Mutex<HashMap<u64, Thread>> {
    THREAD_REGISTRY.get_or_init(|| Mutex::new(HashMap::new()))
}

fn register_thread(token: u64, thread: Thread) {
    let mut map = registry().lock().expect("thread registry poisoned");
    map.insert(token, thread);
}

fn unregister_thread(token: u64) {
    let mut map = registry().lock().expect("thread registry poisoned");
    map.remove(&token);
}

pub fn current_thread_token() -> u64 {
    THREAD_TOKEN.with(|t| *t)
}

pub fn unpark_thread(token: u64) -> bool {
    let target = {
        let map = registry().lock().expect("thread registry poisoned");
        map.get(&token).cloned()
    };
    if let Some(thread) = target {
        thread.unpark();
        true
    } else {
        false
    }
}

pub fn park_current_thread() {
    thread::park();
}

pub fn park_current_thread_for(duration: Duration) {
    thread::park_timeout(duration);
}

pub fn monotonic_millis() -> u64 {
    let start = START_TIME.get_or_init(Instant::now);
    start.elapsed().as_millis() as u64
}

pub fn unix_time_seconds() -> i64 {
    match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(d) => d.as_secs() as i64,
        Err(_) => 0,
    }
}

pub struct PlatformThread<T> {
    handle: Option<JoinHandle<T>>,
}

impl<T> PlatformThread<T> {
    pub fn join(mut self) -> std::thread::Result<T> {
        let handle =
            self.handle.take().expect("thread handle already consumed");
        handle.join()
    }
}

pub fn spawn_platform<F, T>(f: F) -> PlatformThread<T>
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
{
    PlatformThread {
        handle: Some(thread::spawn(move || {
            let token = current_thread_token();
            let out = f();
            unregister_thread(token);
            out
        })),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Mutex};
    use std::time::Duration;

    #[test]
    fn spawn_platform_runs_on_os_thread() {
        let values = Arc::new(Mutex::new(Vec::new()));
        let values_t = values.clone();
        let thread = spawn_platform(move || {
            values_t.lock().expect("lock values").push(42);
            7usize
        });

        let out = thread.join().expect("thread should join");
        assert_eq!(out, 7);
        let got = values.lock().expect("lock values").clone();
        assert_eq!(got, vec![42]);
    }

    #[test]
    fn unpark_wakes_parked_thread() {
        let token_slot = Arc::new(Mutex::new(0u64));
        let token_slot_t = token_slot.clone();
        let t = spawn_platform(move || {
            let token = current_thread_token();
            *token_slot_t.lock().expect("lock token slot") = token;
            park_current_thread();
            9usize
        });

        let token = loop {
            let token = *token_slot.lock().expect("lock token slot");
            if token != 0 {
                break token;
            }
            thread::sleep(Duration::from_millis(1));
        };
        assert!(unpark_thread(token));
        assert_eq!(t.join().expect("join parked thread"), 9);
    }
}
