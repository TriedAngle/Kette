use std::{
    cell::Cell,
    sync::{
        atomic::{
            AtomicU8,
            Ordering::{AcqRel, Acquire, Relaxed, Release},
        },
        Condvar, Mutex,
    },
};

use crate::{Handle, Value};

const PARKED: u8 = 0b01;
const TOKEN: u8 = 0b10;
#[derive(Debug, Default)]
pub struct NativeParker {
    state: AtomicU8,
    lock: Mutex<()>,
    cv: Condvar,
    blocker: Cell<Option<Handle<Value>>>,
}

// SAFETY: this is safe
unsafe impl Send for NativeParker {}
// SAFETY: this is safe
unsafe impl Sync for NativeParker {}

impl NativeParker {
    #[must_use] 
    pub fn new() -> Self {
        Self {
            state: AtomicU8::new(0),
            lock: Mutex::new(()),
            cv: Condvar::new(),
            blocker: Cell::new(None),
        }
    }

    pub fn park(&self, obj: Handle<Value>) {
        self.blocker.set(Some(obj));

        // Fast path: unpark before park => just ignore
        if self.try_consume_token() {
            self.blocker.set(None);
            return;
        }

        self.state.fetch_or(PARKED, Release);

        if self.try_consume_token() {
            self.state.fetch_and(!PARKED, AcqRel);
            self.blocker.set(None);
            return;
        }

        let mut guard = self.lock.lock().expect("locking works");
        loop {
            guard = self.cv.wait(guard).expect("waiting works");

            if self.try_consume_token() {
                break;
            }
        }
        drop(guard);

        self.state.fetch_and(!PARKED, AcqRel);
        self.blocker.set(None);
    }

    #[inline]
    fn try_consume_token(&self) -> bool {
        let mut s = self.state.load(Acquire);
        while s & TOKEN != 0 {
            match self.state.compare_exchange_weak(
                s,
                s & !TOKEN,
                AcqRel,
                Relaxed,
            ) {
                Ok(_) => return true,
                Err(cur) => s = cur,
            }
        }
        false
    }

    pub fn unpark(&self) {
        let prev = self.state.fetch_or(TOKEN, Release);

        if prev & PARKED != 0 {
            let _g = self.lock.lock().expect("locking works");
            self.cv.notify_one();
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{Header, HeapValue, NativeThread, ObjectType};

    use super::*;
    use std::sync::atomic::{AtomicBool, Ordering::SeqCst};
    use std::sync::{mpsc, Arc};
    use std::thread;
    use std::time::{Duration, Instant};

    fn make_parker() -> Arc<NativeParker> {
        Arc::new(NativeParker::new())
    }

    #[test]
    fn token_is_consumed_when_present() {
        let p = make_parker();

        p.state.store(TOKEN, Release);
        assert!(p.try_consume_token(), "expected to consume the token");
        assert_eq!(
            p.state.load(Acquire) & TOKEN,
            0,
            "token bit should be cleared"
        );
    }

    #[test]
    fn unpark_sets_token_when_not_parked() {
        let p = make_parker();

        p.state.store(0, Relaxed);
        p.unpark();

        assert_ne!(
            p.state.load(Acquire) & TOKEN,
            0,
            "token should be set by unpark()"
        );
        assert!(
            p.try_consume_token(),
            "token should be consumable after unpark()"
        );
        assert_eq!(
            p.state.load(Relaxed) & TOKEN,
            0,
            "token should be cleared after consumption"
        );
    }

    #[test]
    fn unpark_notifies_when_parked() {
        let p = make_parker();
        let woke = Arc::new(AtomicBool::new(false));
        let woke2 = woke.clone();
        let p2 = p.clone();

        let waiter = thread::spawn(move || {
            let g = p2.lock.lock().expect("lock poisoned");
            let (_g, timeout_res) =
                p2.cv.wait_timeout(g, Duration::from_millis(500)).unwrap();
            if !timeout_res.timed_out() {
                woke2.store(true, SeqCst);
            }
        });

        thread::sleep(Duration::from_millis(50));

        p.state.fetch_or(PARKED, Release);
        p.unpark();

        waiter.join().unwrap();
        assert!(
            woke.load(SeqCst),
            "waiter should have been notified by unpark() when PARKED"
        );
    }

    #[test]
    fn end_to_end_like_park_loop_consumes_token_and_clears_parked() {
        let p = make_parker();
        let done = Arc::new(AtomicBool::new(false));
        let done2 = done.clone();
        let p2 = p.clone();

        let t = thread::spawn(move || {
            if p2.try_consume_token() {
                done2.store(true, SeqCst);
                return;
            }

            p2.state.fetch_or(PARKED, Release);

            if p2.try_consume_token() {
                p2.state.fetch_and(!PARKED, AcqRel);
                done2.store(true, SeqCst);
                return;
            }

            let mut guard = p2.lock.lock().unwrap();
            loop {
                guard = p2.cv.wait(guard).unwrap();
                if p2.try_consume_token() {
                    break;
                }
            }
            drop(guard);

            p2.state.fetch_and(!PARKED, AcqRel);
            done2.store(true, SeqCst);
        });

        thread::sleep(Duration::from_millis(50));

        let start = Instant::now();
        p.unpark();

        while !done.load(SeqCst) && start.elapsed() < Duration::from_secs(1) {
            thread::sleep(Duration::from_millis(5));
        }

        t.join().unwrap();
        assert!(
            done.load(SeqCst),
            "park-like loop should have completed after unpark()"
        );
        assert_eq!(
            p.state.load(Acquire) & (PARKED | TOKEN),
            0,
            "PARKED and TOKEN should be cleared at end"
        );
    }

    #[test]
    fn only_one_consumer_wins_the_token() {
        let p = make_parker();
        p.state.store(TOKEN, Release);

        let winners = Arc::new(AtomicU8::new(0));
        let mut joins = Vec::new();

        for _ in 0..8 {
            let p2 = p.clone();
            let winners2 = winners.clone();
            joins.push(thread::spawn(move || {
                if p2.try_consume_token() {
                    winners2.fetch_add(1, AcqRel);
                }
            }));
        }

        for j in joins {
            j.join().unwrap();
        }

        assert_eq!(
            winners.load(Acquire),
            1,
            "exactly one thread should consume the token"
        );
        assert_eq!(
            p.state.load(Acquire) & TOKEN,
            0,
            "token bit must be cleared after consumption"
        );
    }

    fn dummy_view() -> Handle<HeapValue> {
        static mut DUMMY: HeapValue = HeapValue {
            header: Header::new_object(ObjectType::Max),
        };
        unsafe { Handle::from_ptr(&raw mut DUMMY) }
    }

    #[test]
    fn park_blocks_then_unparks_with_native_spawn() {
        let (tx, rx) = mpsc::channel::<(Arc<NativeParker>, Handle<Value>)>();

        let returned = Arc::new(AtomicBool::new(false));
        let returned2 = returned.clone();

        let nt = NativeThread::spawn(move || {
            let (parker, obj) = rx.recv().expect("parker/object not sent");
            // This should block until unpark().
            parker.park(obj);
            returned2.store(true, SeqCst);
        });

        let parker = Arc::new(NativeParker::new());

        tx.send((parker.clone(), dummy_view().into())).unwrap();
        std::thread::sleep(Duration::from_millis(50));

        assert!(
            !returned.load(SeqCst),
            "park() returned too early without unpark"
        );

        parker.unpark();

        let start = Instant::now();
        while !returned.load(SeqCst) && start.elapsed() < Duration::from_secs(1)
        {
            std::thread::sleep(Duration::from_millis(5));
        }
        assert!(
            returned.load(SeqCst),
            "park() did not return after unpark()"
        );

        nt.join();
    }

    #[test]
    fn pre_delivered_token_means_no_block() {
        let (tx, rx) = mpsc::channel::<(Arc<NativeParker>, Handle<Value>)>();
        let returned = Arc::new(AtomicBool::new(false));
        let returned2 = returned.clone();

        let nt = NativeThread::spawn(move || {
            let (parker, obj) = rx.recv().unwrap();
            // park() should observe the pre-set token and return immediately.
            let start = Instant::now();
            parker.park(obj);
            returned2.store(true, SeqCst);
            // Sanity: ensure it really was fast (no blocking).
            assert!(
                start.elapsed() < Duration::from_millis(50),
                "park() took too long despite pre-delivered token"
            );
        });

        let parker = Arc::new(NativeParker::new());

        parker.unpark();

        // Now let the thread call park(); it should return quickly.
        tx.send((parker.clone(), dummy_view().into())).unwrap();

        let start = Instant::now();
        while !returned.load(SeqCst) && start.elapsed() < Duration::from_secs(1)
        {
            std::thread::sleep(Duration::from_millis(5));
        }
        assert!(
            returned.load(SeqCst),
            "park() did not return with pre-delivered token"
        );

        nt.join();
    }

    #[test]
    fn back_to_back_unparks_before_wake_do_not_leave_token() {
        let (tx, rx) = mpsc::channel::<(Arc<NativeParker>, Handle<Value>)>();
        let phase1_done = Arc::new(AtomicBool::new(false));
        let phase1_done2 = phase1_done.clone();

        let nt = NativeThread::spawn(move || {
            let (parker, obj1) = rx.recv().unwrap();

            parker.park(obj1);
            phase1_done2.store(true, SeqCst);

            let obj2 = dummy_view();
            parker.park(obj2.into());
        });

        let parker = Arc::new(NativeParker::new());
        tx.send((parker.clone(), dummy_view().into())).unwrap();

        std::thread::sleep(Duration::from_millis(50));
        parker.unpark();
        parker.unpark();

        let start = Instant::now();
        while !phase1_done.load(SeqCst)
            && start.elapsed() < Duration::from_secs(1)
        {
            std::thread::sleep(Duration::from_millis(5));
        }
        assert!(
            phase1_done.load(SeqCst),
            "first park() did not complete after unpark()"
        );

        std::thread::sleep(Duration::from_millis(50));
        parker.unpark();

        nt.join();
    }

    #[test]
    fn second_unpark_after_first_wake_makes_next_park_instant() {
        let (tx, rx) = mpsc::channel::<(Arc<NativeParker>, Handle<Value>)>();
        let phase1_done = Arc::new(AtomicBool::new(false));
        let phase1_done2 = phase1_done.clone();
        let phase2_returned = Arc::new(AtomicBool::new(false));
        let phase2_returned2 = phase2_returned.clone();

        let nt = NativeThread::spawn(move || {
            let (parker, obj1) = rx.recv().unwrap();

            parker.park(obj1);
            phase1_done2.store(true, SeqCst);

            let obj2 = dummy_view();
            let t0 = Instant::now();
            parker.park(obj2.into());
            phase2_returned2.store(true, SeqCst);
            assert!(
                t0.elapsed() < Duration::from_millis(50),
                "second park() should have returned immediately from post-wake token"
            );
        });

        let parker = Arc::new(NativeParker::new());
        tx.send((parker.clone(), dummy_view().into())).unwrap();

        std::thread::sleep(Duration::from_millis(50));
        parker.unpark();

        let start = Instant::now();
        while !phase1_done.load(SeqCst)
            && start.elapsed() < Duration::from_secs(1)
        {
            std::thread::sleep(Duration::from_millis(5));
        }
        assert!(
            phase1_done.load(SeqCst),
            "first park() did not complete after unpark()"
        );

        parker.unpark();

        let start2 = Instant::now();
        while !phase2_returned.load(SeqCst)
            && start2.elapsed() < Duration::from_secs(1)
        {
            std::thread::sleep(Duration::from_millis(5));
        }
        assert!(
            phase2_returned.load(SeqCst),
            "second park() did not return immediately"
        );

        nt.join();
    }

    #[test]
    fn unpark_from_another_native_thread() {
        let (tx, rx) = mpsc::channel::<(Arc<NativeParker>, Handle<Value>)>();
        let woke = Arc::new(AtomicBool::new(false));
        let woke2 = woke.clone();

        let waiter = NativeThread::spawn(move || {
            let (parker, obj) = rx.recv().unwrap();
            parker.park(obj);
            woke2.store(true, SeqCst);
        });

        let parker = Arc::new(NativeParker::new());
        tx.send((parker.clone(), dummy_view().into())).unwrap();

        let signaller = NativeThread::spawn({
            let parker = parker.clone();
            move || {
                std::thread::sleep(Duration::from_millis(60));
                parker.unpark();
            }
        });

        let start = Instant::now();
        while !woke.load(SeqCst) && start.elapsed() < Duration::from_secs(1) {
            std::thread::sleep(Duration::from_millis(5));
        }
        assert!(
            woke.load(SeqCst),
            "waiter was not woken by unpark from another native thread"
        );

        waiter.join();
        signaller.join();
    }
}
