use std::{
    cell::UnsafeCell,
    ops::Deref,
    sync::Arc,
    thread::{self, JoinHandle},
    time::Duration,
};

use parking_lot::{Condvar, Mutex};

use crate::{
    ExecutionState, Handle, Header, HeapObject, HeapProxy, Interpreter,
    NativeParker, Object, Tagged, VMProxy, Visitable,
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
pub struct ThreadShared {
    pub info: Mutex<ThreadInfo>,
    pub parker: NativeParker,
    pub user_thread: Handle<ThreadObject>,
}

#[derive(Debug)]
pub struct ThreadProxy(pub Arc<ThreadShared>);

impl Deref for ThreadProxy {
    type Target = ThreadShared;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[repr(C)]
pub struct VMThread {
    pub inner: Arc<ThreadShared>,
    pub native: Option<Arc<NativeThread>>,
    pub carrier: Option<Arc<VMThread>>,
}

#[repr(C)]
pub struct NativeThread {
    handle: UnsafeCell<Option<JoinHandle<()>>>,
    done: (Mutex<bool>, Condvar),
}

// SAFETY: this is safe
unsafe impl Send for NativeThread {}
// SAFETY: this is safe
unsafe impl Sync for NativeThread {}

impl ThreadShared {
    pub fn new(
        user_thread: Handle<ThreadObject>,
        is_virtual: bool,
    ) -> Arc<Self> {
        let info = ThreadInfo {
            state: ThreadState::Created,
            is_vm: true,
            is_virtual,
            thread_id: 0,
        };
        let parker = NativeParker::new();
        Arc::new(Self {
            info: Mutex::new(info),
            parker,
            user_thread,
        })
    }
}

impl VMThread {
    pub fn new_main() -> Self {
        // SAFETY: we will not dereference this
        let thread_obj = unsafe { Handle::null() };
        let shared = ThreadShared::new(thread_obj, false);
        // thread_id is guaranteed to be nonzero, thus we use 0 for main
        shared.info.lock().thread_id = 0;

        Self {
            inner: shared,
            native: None,
            carrier: None,
        }
    }
    pub fn new_native(
        vm: VMProxy,
        heap: HeapProxy,
        user_thread: Handle<ThreadObject>,
        executor: ExecutionState,
    ) -> Self {
        let shared = ThreadShared::new(user_thread, false);
        let proxy = ThreadProxy(shared.clone());
        let native = NativeThread::spawn(move || {
            {
                let mut info = proxy.info.lock();
                let thread_id = thread::current().id();
                // SAFETY: this is safe, the layout is the same, thread_id is nonzero
                // furthermore, this allows us to model main as 0
                let id: u64 = unsafe { std::mem::transmute(thread_id) };
                info.thread_id = id;
            }
            let _interpreter = Interpreter::new(vm, proxy, heap, executor);
            // executor.run();
        });
        Self {
            inner: shared,
            native: Some(native),
            carrier: None,
        }
    }

    // a virtual spawns without a native nor a carrier, the carrier is set when running.
    pub fn new_virtual(
        user_thread: Handle<ThreadObject>,
        _executor: ExecutionState,
    ) -> Self {
        let shared = ThreadShared::new(user_thread, true);
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

        // SAFETY: directly at initialization, it is owned
        unsafe { jt.handle.get().as_mut().unwrap_unchecked().replace(h) };
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
        // SAFETY: thread alive => exists
        if let Some(h) =
            unsafe { self.handle.get().as_mut().unwrap_unchecked().take() }
        {
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
        // SAFETY: this is safe as long as thread is alive
        // and if it is not alive, it is also not accessible
        unsafe { self.handle.get().as_mut().unwrap_unchecked() }
            .as_ref()
            .map(|handle| handle.thread().clone())
    }

    // pub fn new_main() -> Self {
    //
    // }
}
