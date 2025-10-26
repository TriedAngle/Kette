use crate::{Actor, ActorId, ActorState};
use parking_lot::{Condvar, Mutex, RwLock};
use std::{
    collections::{HashMap, VecDeque},
    sync::{
        Arc,
        atomic::{AtomicBool, AtomicU64, Ordering},
    },
    thread::{self, JoinHandle},
    time::{Duration, Instant},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct WorkerId(pub u64);

#[derive(Clone)]
struct WorkItem {
    actor: Arc<Actor>,
}

struct Worker {
    id: WorkerId,
    local: Mutex<VecDeque<WorkItem>>,
    has_work: Condvar,
    should_stop: AtomicBool,
    dedicated_for: Mutex<Option<ActorId>>, // Some(id) == dedicated; None == pool
    handle: Mutex<Option<JoinHandle<()>>>,
}

unsafe impl Send for Worker {}
unsafe impl Sync for Worker {}

impl Worker {
    fn new(id: WorkerId) -> Arc<Self> {
        Arc::new(Self {
            id,
            local: Mutex::new(VecDeque::new()),
            has_work: Condvar::new(),
            should_stop: AtomicBool::new(false),
            dedicated_for: Mutex::new(None),
            handle: Mutex::new(None),
        })
    }

    fn push(&self, w: WorkItem) {
        {
            let mut q = self.local.lock();
            q.push_front(w);
        }
        self.has_work.notify_one();
    }

    fn pop(&self) -> Option<WorkItem> {
        self.local.lock().pop_front()
    }

    fn steal_back(&self) -> Option<WorkItem> {
        self.local.lock().pop_back()
    }
}

#[derive(Clone, Copy)]
pub struct ScaleConfig {
    /// If avg backlog per non-dedicated worker exceeds this, spawn a worker.
    pub spawn_backlog_threshold: usize,
    /// If a pool worker is idle for this long, it exits.
    pub retire_after_idle: Duration,
    /// Upper bound of pool workers (excluding main + dedicated).
    pub max_pool_workers: usize,
}

/// Scheduler that manages workers and queues.
pub struct Scheduler {
    main: Arc<Worker>,
    pool: Mutex<Vec<Arc<Worker>>>,
    dedicated: Mutex<HashMap<ActorId, Arc<Worker>>>,
    id_gen: AtomicU64,
    scale: ScaleConfig,
    // TODO: we probably don't need hooks in practice, remove them
    hooks: RwLock<HashMap<ActorId, Arc<dyn Fn(&Arc<Actor>) + Send + Sync>>>,
}

impl Scheduler {
    pub fn new(scale: ScaleConfig) -> Self {
        let main = Worker::new(WorkerId(0));
        Self {
            main,
            pool: Mutex::new(Vec::new()),
            dedicated: Mutex::new(HashMap::new()),
            id_gen: AtomicU64::new(0),
            scale,
            hooks: RwLock::new(HashMap::new()),
        }
    }

    /// Register a simple run hook for an actor (optional, handy for tests).
    pub fn register_hook<F>(&self, actor: &Arc<Actor>, f: F)
    where
        F: Fn(&Arc<Actor>) + Send + Sync + 'static,
    {
        self.hooks.write().insert(actor.id, Arc::new(f));
    }

    /// Create a new pool worker thread.
    fn spawn_pool_worker(self: &Arc<Self>) -> Arc<Worker> {
        let id = WorkerId(self.id_gen.fetch_add(1, Ordering::Relaxed) + 1); // start from 1
        let w = Worker::new(id);
        let me = Arc::clone(self);
        let w_clone = Arc::clone(&w);
        let handle = thread::Builder::new()
            .name(format!("sched-worker-{}", id.0))
            .spawn(move || me.worker_loop(w_clone, false))
            .expect("spawn worker");
        *w.handle.lock() = Some(handle);
        self.pool.lock().push(Arc::clone(&w));
        w
    }

    /// Create a dedicated worker thread for a specific actor.
    fn spawn_dedicated(self: &Arc<Self>, actor_id: ActorId) -> Arc<Worker> {
        let id = WorkerId(self.id_gen.fetch_add(1, Ordering::Relaxed) + 1);
        let w = Worker::new(id);
        *w.dedicated_for.lock() = Some(actor_id);
        let me = Arc::clone(self);
        let w_clone = Arc::clone(&w);
        let handle = thread::Builder::new()
            .name(format!("sched-dedicated-{}-for-{}", id.0, actor_id.0))
            .spawn(move || me.worker_loop(w_clone, true))
            .expect("spawn dedicated");
        *w.handle.lock() = Some(handle);
        self.dedicated.lock().insert(actor_id, Arc::clone(&w));
        w
    }

    /// Drive the main-thread worker **once**. Returns true if something ran.
    pub fn run_main_once(&self) -> bool {
        if let Some(work) = self.main.pop() {
            self.run_actor(work.actor);
            true
        } else {
            // Small, opportunistic steal from pool to keep UI/main alive.
            let pool_snapshot = self.pool.lock().clone();
            for w in pool_snapshot {
                if let Some(work) = w.steal_back() {
                    self.run_actor(work.actor);
                    return true;
                }
            }
            false
        }
    }

    /// Drive the main thread until nothing runs for `idle_for` duration.
    pub fn run_main_until_idle(&self, idle_for: Duration) {
        let deadline = Instant::now() + idle_for;
        loop {
            if self.run_main_once() {
                continue;
            }
            if Instant::now() >= deadline {
                break;
            }
            // Short nap so we don’t spin.
            thread::sleep(Duration::from_millis(1));
        }
    }

    /// Submit an actor for execution. Honors dedicated/pinned if present.
    pub fn submit(self: &Arc<Self>, actor: Arc<Actor>) {
        let (actor_id, pinned, dedicated) = {
            let mut info = actor.info.write();
            if matches!(info.state, ActorState::Dead) {
                return;
            }
            info.state = ActorState::Active;
            (actor.id, info.pinned, info.dedicated)
        };

        if dedicated.is_some() {
            let w = if let Some(w) = { self.dedicated.lock().get(&actor_id).cloned() } {
                w
            } else {
                self.spawn_dedicated(actor_id)
            };
            debug_assert_eq!(*w.dedicated_for.lock(), Some(actor_id));
            w.push(WorkItem { actor });
            return;
        }

        if let Some(wid) = pinned {
            if wid == WorkerId(0) {
                self.main.push(WorkItem { actor });
                return;
            }
            if let Some(w) = {
                let pool = self.pool.lock();
                pool.iter().find(|w| w.id == wid).cloned()
            } {
                w.push(WorkItem { actor });
                return;
            } else {
                let w = self.spawn_pool_worker();
                {
                    let mut info = actor.info.write();
                    info.pinned = Some(w.id);
                }
                w.push(WorkItem { actor });
                return;
            }
        }

        let w = self.pick_or_spawn_pool_worker();
        w.push(WorkItem { actor });
    }

    pub fn pin_actor(&self, actor: &Arc<Actor>, worker: WorkerId) {
        let mut info = actor.info.write();
        info.pinned = Some(worker);
    }

    pub fn dedicate_actor(self: &Arc<Self>, actor: &Arc<Actor>) {
        let mut info = actor.info.write();
        if info.dedicated.is_none() {
            let w = self.spawn_dedicated(actor.id);
            info.dedicated = Some(w.id);
        }
    }

    pub fn undedicate_actor(&self, actor: &Arc<Actor>) {
        let mut info = actor.info.write();
        if let Some(_wid) = info.dedicated.take() {
            if let Some(w) = self.dedicated.lock().remove(&actor.id) {
                w.should_stop.store(true, Ordering::Relaxed);
                if let Some(h) = w.handle.lock().take() {
                    let _ = h.join();
                }
            }
        }
    }

    pub fn unpin_actor(&self, actor: &Arc<Actor>) {
        actor.info.write().pinned = None;
    }

    pub fn shutdown(&self) {
        for w in self.pool.lock().drain(..) {
            w.should_stop.store(true, Ordering::Relaxed);
            if let Some(h) = w.handle.lock().take() {
                let _ = h.join();
            }
        }
        for (_, w) in self.dedicated.lock().drain() {
            w.should_stop.store(true, Ordering::Relaxed);
            if let Some(h) = w.handle.lock().take() {
                let _ = h.join();
            }
        }
    }

    fn worker_loop(self: Arc<Self>, me: Arc<Worker>, dedicated: bool) {
        let retire_after = self.scale.retire_after_idle;
        let mut last_work = Instant::now();

        loop {
            if me.should_stop.load(Ordering::Relaxed) {
                break;
            }

            if let Some(work) = me.pop() {
                self.run_actor(work.actor);
                last_work = Instant::now();
                continue;
            }

            if !dedicated {
                if let Some(work) = self.try_steal(&me) {
                    self.run_actor(work.actor);
                    last_work = Instant::now();
                    continue;
                }
            }

            let timeout = Duration::from_millis(10);
            {
                let mut guard = me.local.lock();
                let _ = me.has_work.wait_for(&mut guard, timeout);
            }

            if !dedicated && Instant::now().duration_since(last_work) >= retire_after {
                let mut pool = self.pool.lock();
                if let Some(pos) = pool.iter().position(|w| w.id == me.id) {
                    pool.swap_remove(pos);
                }
                break;
            }
        }
    }

    fn try_steal(&self, me: &Arc<Worker>) -> Option<WorkItem> {
        let pool_snapshot = self.pool.lock().clone();
        for w in pool_snapshot {
            if w.id != me.id {
                if let Some(work) = w.steal_back() {
                    return Some(work);
                }
            }
        }
        None
    }

    fn run_actor(&self, actor: Arc<Actor>) {
        {
            let mut info = actor.info.write();
            if matches!(info.state, ActorState::Dead) {
                return;
            }
            info.state = ActorState::Active;
        }

        if let Some(h) = self.hooks.read().get(&actor.id).cloned() {
            h(&actor);
        }

        {
            let mut info = actor.info.write();
            if !matches!(info.state, ActorState::Dead) {
                info.state = ActorState::Stale;
            }
        }
    }

    fn pick_or_spawn_pool_worker(self: &Arc<Self>) -> Arc<Worker> {
        let pool = self.pool.lock();
        if pool.is_empty() {
            if self.scale.max_pool_workers > 0 {
                drop(pool);
                return self.spawn_pool_worker();
            } else {
                return Arc::clone(&self.main);
            }
        }

        let total_backlog: usize = pool.iter().map(|w| w.local.lock().len()).sum();
        let avg = total_backlog / pool.len().max(1);

        if avg >= self.scale.spawn_backlog_threshold && pool.len() < self.scale.max_pool_workers {
            drop(pool);
            return self.spawn_pool_worker();
        }

        let (best_idx, _) = pool
            .iter()
            .enumerate()
            .map(|(i, w)| (i, w.local.lock().len()))
            .min_by_key(|(_, n)| *n)
            .unwrap();
        Arc::clone(&pool[best_idx])
    }
}

#[cfg(test)]
mod tests {
    use crate::{ActorInfo, Header, Heap};

    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    fn mk_actor(id: u64) -> Arc<Actor> {
        Arc::new(Actor {
            header: Header::zeroed(),
            id: ActorId(id),
            heap: Heap::zeroed(),
            info: RwLock::new(ActorInfo {
                pinned: None,
                dedicated: None,
                state: ActorState::Stale,
            }),
            fibers: Vec::new(),
        })
    }

    #[test]
    fn main_thread_executes_pinned_work() {
        let sched = Arc::new(Scheduler::new(ScaleConfig {
            spawn_backlog_threshold: 4,
            retire_after_idle: Duration::from_millis(50),
            max_pool_workers: 2,
        }));

        let a = mk_actor(1);
        let ran = Arc::new(AtomicUsize::new(0));
        {
            let ran = ran.clone();
            sched.register_hook(&a, move |_| {
                ran.fetch_add(1, Ordering::SeqCst);
            });
        }

        sched.pin_actor(&a, WorkerId(0));
        sched.submit(a.clone());

        sched.run_main_until_idle(Duration::from_millis(10));

        assert_eq!(ran.load(Ordering::SeqCst), 1);
        assert!(matches!(a.info.read().state, ActorState::Stale));
        sched.shutdown();
    }

    #[test]
    fn pool_workers_steal_and_run() {
        let sched = Arc::new(Scheduler::new(ScaleConfig {
            spawn_backlog_threshold: 1, // spawn quickly
            retire_after_idle: Duration::from_millis(50),
            max_pool_workers: 4,
        }));

        let n = 8;
        let ran = Arc::new(AtomicUsize::new(0));

        let mut actors = Vec::new();
        for i in 0..n {
            let a = mk_actor(i as u64);
            let ran = ran.clone();
            sched.register_hook(&a, move |_| {
                ran.fetch_add(1, Ordering::SeqCst);
            });
            actors.push(a);
        }

        for a in &actors {
            sched.submit(a.clone());
        }

        // Let pool workers process.
        thread::sleep(Duration::from_millis(100));

        assert_eq!(ran.load(Ordering::SeqCst), n);
        for a in &actors {
            assert!(matches!(a.info.read().state, ActorState::Stale));
        }
        sched.shutdown();
    }

    #[test]
    fn dedicated_worker_isolated() {
        let sched = Arc::new(Scheduler::new(ScaleConfig {
            spawn_backlog_threshold: 2,
            retire_after_idle: Duration::from_millis(50),
            max_pool_workers: 1,
        }));

        let a_ded = mk_actor(10);
        let a_pool = mk_actor(11);

        let d_runs = Arc::new(AtomicUsize::new(0));
        let p_runs = Arc::new(AtomicUsize::new(0));

        {
            let d_runs = d_runs.clone();
            sched.register_hook(&a_ded, move |_| {
                d_runs.fetch_add(1, Ordering::SeqCst);
            });
        }
        {
            let p_runs = p_runs.clone();
            sched.register_hook(&a_pool, move |_| {
                p_runs.fetch_add(1, Ordering::SeqCst);
            });
        }

        sched.dedicate_actor(&a_ded);

        for _ in 0..4 {
            sched.submit(a_ded.clone());
            sched.submit(a_pool.clone());
        }

        thread::sleep(Duration::from_millis(120));

        assert!(d_runs.load(Ordering::SeqCst) >= 1);
        assert!(p_runs.load(Ordering::SeqCst) >= 1);

        assert!(sched.dedicated.lock().contains_key(&a_ded.id));
        sched.shutdown();
    }

    #[test]
    fn pool_scales_up_and_retires() {
        let sched = Arc::new(Scheduler::new(ScaleConfig {
            spawn_backlog_threshold: 2, // encourage spawn
            retire_after_idle: Duration::from_millis(60),
            max_pool_workers: 3,
        }));

        let ran = Arc::new(AtomicUsize::new(0));
        // Enqueue enough actors to trigger scaling up.
        for i in 0..6 {
            let a = mk_actor(100 + i);
            let ran = ran.clone();
            sched.register_hook(&a, move |_| {
                ran.fetch_add(1, Ordering::SeqCst);
                // simulate tiny work
                thread::sleep(Duration::from_millis(2));
            });
            sched.submit(a);
        }

        // Give time to scale and process
        thread::sleep(Duration::from_millis(150));

        assert_eq!(ran.load(Ordering::SeqCst), 6);

        thread::sleep(Duration::from_millis(100));
        let pool_len = sched.pool.lock().len();
        assert!(
            pool_len <= 1,
            "pool should have retired to small size, got {}",
            pool_len
        );

        sched.shutdown();
    }

    fn parse_worker_id_from_name(n: &str) -> Option<u64> {
        // "sched-worker-{id}" or "sched-dedicated-{id}-for-{actor}"
        if let Some(rest) = n.strip_prefix("sched-worker-") {
            return rest.parse::<u64>().ok();
        }
        if let Some(rest) = n.strip_prefix("sched-dedicated-") {
            let id_part = rest.split('-').next().unwrap_or("");
            return id_part.parse::<u64>().ok();
        }
        None
    }

    fn is_dedicated_name(n: &str) -> bool {
        n.starts_with("sched-dedicated-")
    }

    #[test]
    fn pinned_to_main_stays_on_main() {
        let sched = Arc::new(Scheduler::new(ScaleConfig {
            spawn_backlog_threshold: 1,
            retire_after_idle: Duration::from_millis(50),
            max_pool_workers: 2,
        }));

        // Make sure at least one pool worker exists so stealing would be possible
        // if the item were not pinned to main.
        let _w1 = sched.spawn_pool_worker();

        let a = mk_actor(2000);

        // record every thread name that runs this actor
        let seen = Arc::new(Mutex::new(Vec::<String>::new()));
        {
            let seen = seen.clone();
            sched.register_hook(&a, move |_| {
                let name = thread::current()
                    .name()
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| "<main>".to_string());
                seen.lock().push(name);
            });
        }

        // Pin to main and submit multiple times.
        sched.pin_actor(&a, WorkerId(0));
        for _ in 0..5 {
            sched.submit(a.clone());
        }

        // Drive main long enough to process.
        sched.run_main_until_idle(Duration::from_millis(30));

        // Assert all runs were on the main thread (i.e., not one of our named workers).
        let names = seen.lock().clone();
        assert!(!names.is_empty(), "actor should have run at least once");
        for n in names {
            assert!(
                !n.starts_with("sched-worker-") && !n.starts_with("sched-dedicated-"),
                "found execution off main thread: {}",
                n
            );
        }

        sched.shutdown();
    }

    #[test]
    fn dedicated_actor_runs_only_on_its_dedicated_worker() {
        let sched = Arc::new(Scheduler::new(ScaleConfig {
            spawn_backlog_threshold: 1,
            retire_after_idle: Duration::from_millis(80),
            max_pool_workers: 2,
        }));

        // Create some pool capacity so the test can detect if a steal ever occurred.
        let _w1 = sched.spawn_pool_worker();
        let _w2 = sched.spawn_pool_worker();

        let a = mk_actor(3000);

        // Dedicate and capture observed worker ids and names.
        sched.dedicate_actor(&a);

        let seen_ids = Arc::new(Mutex::new(Vec::<u64>::new()));
        let seen_names = Arc::new(Mutex::new(Vec::<String>::new()));

        {
            let seen_ids = seen_ids.clone();
            let seen_names = seen_names.clone();
            sched.register_hook(&a, move |_| {
                let name = thread::current()
                    .name()
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| "<main>".to_string());
                if let Some(id) = parse_worker_id_from_name(&name) {
                    seen_ids.lock().push(id);
                }
                seen_names.lock().push(name);
            });
        }

        for _ in 0..6 {
            sched.submit(a.clone());
        }

        thread::sleep(Duration::from_millis(120));

        let names = seen_names.lock().clone();
        let ids = seen_ids.lock().clone();

        assert!(!names.is_empty(), "dedicated actor should have run");
        // All executions must be on a dedicated thread (never main or pool).
        for n in &names {
            assert!(
                is_dedicated_name(n),
                "dedicated actor ran on non-dedicated thread: {}",
                n
            );
        }
        // All runs should be on the *same* dedicated worker id.
        let mut uniq = ids.clone();
        uniq.sort_unstable();
        uniq.dedup();
        assert_eq!(
            uniq.len(),
            1,
            "dedicated actor should always run on the same dedicated worker, got {:?}",
            ids
        );

        sched.shutdown();
    }

    #[test]
    fn stealing_occurs_between_pool_workers() {
        let sched = Arc::new(Scheduler::new(ScaleConfig {
            spawn_backlog_threshold: 64, // don't auto-spawn; we'll do it manually
            retire_after_idle: Duration::from_millis(200),
            max_pool_workers: 4,
        }));

        // Manually create two pool workers with known IDs.
        let w1 = sched.spawn_pool_worker(); // source victim
        let w2 = sched.spawn_pool_worker(); // thief candidate

        let total = 32usize;

        let ran_on_w1 = Arc::new(AtomicUsize::new(0));
        let ran_on_w2 = Arc::new(AtomicUsize::new(0));

        for i in 0..total {
            let a = mk_actor(4000 + i as u64);

            let r1 = ran_on_w1.clone();
            let r2 = ran_on_w2.clone();
            let w1_id = w1.id.0;
            let w2_id = w2.id.0;

            sched.register_hook(&a, move |_| {
                // Simulate a little work so backlog remains visible to thieves.
                std::thread::sleep(std::time::Duration::from_millis(5));

                let thread_id = std::thread::current();
                let name = thread_id.name().unwrap_or("<main>");
                if let Some(id) = super::tests::parse_worker_id_from_name(name) {
                    if id == w1_id {
                        r1.fetch_add(1, Ordering::SeqCst);
                    } else if id == w2_id {
                        r2.fetch_add(1, Ordering::SeqCst);
                    }
                }
            });

            // Force initial placement on w1 (owner still allows steal afterward).
            {
                let mut info = a.info.write();
                info.pinned = Some(w1.id);
            }
            sched.submit(a);
        }

        // Give workers time to process and for steals to happen reliably.
        std::thread::sleep(std::time::Duration::from_millis(800));

        let c1 = ran_on_w1.load(Ordering::SeqCst);
        let c2 = ran_on_w2.load(Ordering::SeqCst);

        assert!(c1 + c2 > 0, "no actors ran at all");
        assert!(
            c2 > 0,
            "expected some work to be stolen by w2 from w1's queue, but w2 ran 0 (w1 ran {c1})"
        );

        sched.shutdown();
    }
}
