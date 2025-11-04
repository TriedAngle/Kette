use std::{
    cell::UnsafeCell,
    sync::Arc,
    thread::{self, JoinHandle},
    time::Duration,
};

use parking_lot::{Condvar, Mutex};

use crate::{Header, NativeParker, TaggedUsize, VMProxy, View, execution::ExecutionState};

#[derive(Debug)]
pub enum ThreadState {
    Created,
    Running,
    Waiting,
    Dead,
}

#[repr(C)]
#[derive(Debug)]
pub struct ThreadInfo {
    pub state: ThreadState,
    pub is_vm: bool,
    pub is_virtual: bool,
}

/// this is the vm thread object.
/// vm_thread must be a valid pointer to a VMThread
#[repr(C)]
#[derive(Debug)]
pub struct ThreadObject {
    pub header: Header,
    pub vm_thead: TaggedUsize,
}

#[derive(Debug)]
pub struct VMThreadShared {
    pub info: Mutex<ThreadInfo>,
    pub vm: VMProxy,
    pub executor: ExecutionState,
    pub parker: NativeParker,
    pub user_thread: View<ThreadObject>,
}

#[repr(C)]
pub struct VMThread {
    pub inner: Arc<VMThreadShared>,
    pub native: Option<Arc<NativeThread>>,
    pub carrier: Option<Arc<VMThread>>,
}

#[repr(C)]
pub struct NativeThread {
    handle: UnsafeCell<Option<JoinHandle<()>>>,
    done: (Mutex<bool>, Condvar),
}

unsafe impl Send for NativeThread {}
unsafe impl Sync for NativeThread {}

impl VMThreadShared {
    pub fn new(
        vm: VMProxy,
        user_thread: View<ThreadObject>,
        executor: ExecutionState,
        is_virtual: bool,
    ) -> Arc<Self> {
        let info = ThreadInfo {
            state: ThreadState::Created,
            is_vm: true,
            is_virtual,
        };
        let parker = NativeParker::new();
        Arc::new(Self {
            info: Mutex::new(info),
            vm,
            executor,
            parker,
            user_thread,
        })
    }
}

impl VMThread {
    pub fn new_native(
        vm: VMProxy,
        user_thread: View<ThreadObject>,
        executor: ExecutionState,
    ) -> Self {
        let shared = VMThreadShared::new(vm, user_thread, executor, false);
        let thread = shared.clone();
        let native = NativeThread::spawn(move || {
            println!("shared {:?}", thread);
        });
        Self {
            inner: shared,
            native: Some(native),
            carrier: None,
        }
    }

    // a virtual spawns without a native nor a carrier, the carrier is set when running.
    pub fn new_virtual(
        vm: VMProxy,
        user_thread: View<ThreadObject>,
        executor: ExecutionState,
    ) -> Self {
        let shared = VMThreadShared::new(vm, user_thread, executor, true);
        Self {
            inner: shared,
            native: None,
            carrier: None,
        }
    }
}

impl NativeThread {
    pub fn new_empty_thread() -> Arc<Self> {
        Self::spawn(|| {})
    }
    pub fn spawn<F>(f: F) -> Arc<Self>
    where
        F: FnOnce() -> (),
        F: Send + 'static,
    {
        let jt = Arc::new(Self {
            handle: UnsafeCell::new(None),
            done: (Mutex::new(false), Condvar::new()),
        });

        let jt2 = Arc::clone(&jt);
        let h = thread::spawn(move || {
            f();
            let (ref mx, ref cv) = jt2.done;
            *mx.lock() = true;
            cv.notify_all();
        });
        unsafe { jt.handle.get().as_mut().unwrap().replace(h) };
        jt
    }

    pub fn join_timeout(&self, dur: Duration) -> bool {
        // fast path
        {
            if *self.done.0.lock() {
                return true;
            }
        }
        let (ref mx, ref cv) = self.done;
        let mut done = mx.lock();
        let res = cv.wait_for(&mut done, dur);
        !res.timed_out()
    }

    pub fn join(&self) {
        if let Some(h) = unsafe { self.handle.get().as_mut().unwrap().take() } {
            let _ = h.join();
            let (ref mx, ref cv) = self.done;
            *mx.lock() = true;
            cv.notify_all();
            return;
        }

        let (ref mx, ref cv) = self.done;
        let mut done = mx.lock();
        while !*done {
            cv.wait(&mut done);
        }
    }

    pub fn thread(&self) -> Option<thread::Thread> {
        unsafe { self.handle.get().as_mut().unwrap() }
            .as_ref()
            .map(|handle| handle.thread().clone())
    }
}
