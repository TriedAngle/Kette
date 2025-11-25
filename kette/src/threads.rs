use std::{
    cell::UnsafeCell,
    ops::Deref,
    sync::Arc,
    thread::{self, JoinHandle},
    time::Duration,
};

use parking_lot::{Condvar, Mutex};

use crate::{
    Handle, Header, HeapObject, NativeParker, Object, Tagged, VMProxy, Visitable,
    executor::{ExecutionState, Executor},
};

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
    pub thread_id: u64,
}

/// this is the vm thread object.
/// vm_thread must be a valid pointer to a VMThread
#[repr(C)]
#[derive(Debug)]
pub struct ThreadObject {
    pub header: Header,
    pub vm_thead: Tagged<*mut VMThread>,
}

impl Visitable for ThreadObject {}
impl Object for ThreadObject {}
impl HeapObject for ThreadObject {}

#[derive(Debug)]
pub struct VMThreadShared {
    pub info: Mutex<ThreadInfo>,
    pub vm: VMProxy,
    pub parker: NativeParker,
    pub user_thread: Handle<ThreadObject>,
}

#[derive(Debug)]
pub struct VMThreadProxy(Arc<VMThreadShared>);

impl Deref for VMThreadProxy {
    type Target = VMThreadShared;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
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
    pub fn new(vm: VMProxy, user_thread: Handle<ThreadObject>, is_virtual: bool) -> Arc<Self> {
        let info = ThreadInfo {
            state: ThreadState::Created,
            is_vm: true,
            is_virtual,
            thread_id: 0,
        };
        let parker = NativeParker::new();
        Arc::new(Self {
            info: Mutex::new(info),
            vm,
            parker,
            user_thread,
        })
    }
}

impl VMThread {
    pub fn new_native(
        vm: VMProxy,
        user_thread: Handle<ThreadObject>,
        executor: ExecutionState,
    ) -> Self {
        let shared = VMThreadShared::new(vm, user_thread, false);
        let proxy = VMThreadProxy(shared.clone());
        let native = NativeThread::spawn(move || {
            {
                let mut info = proxy.info.lock();
                let thread_id = thread::current().id();
                let id: u64 = unsafe { std::mem::transmute(thread_id) };
                info.thread_id = id;
            }
            let executor = Executor::new(proxy, executor);
            executor.run();
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
        user_thread: Handle<ThreadObject>,
        _executor: ExecutionState,
    ) -> Self {
        let shared = VMThreadShared::new(vm, user_thread, true);
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
        F: FnOnce(),
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

    // pub fn new_main() -> Self {
    //
    // }
}
