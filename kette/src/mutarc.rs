use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct MutArc<T> {
    inner: NonNull<MutArcInner<T>>,
}

struct MutArcInner<T> {
    ref_count: AtomicUsize,
    data: T,
}

unsafe impl<T: Send + Sync> Sync for MutArc<T> {}
unsafe impl<T: Send> Send for MutArc<T> {}

impl<T> MutArc<T> {
    pub fn new(data: T) -> Self {
        let inner = Box::new(MutArcInner {
            ref_count: AtomicUsize::new(1),
            data,
        });

        Self {
            inner: NonNull::new(Box::into_raw(inner)).unwrap(),
        }
    }

    fn inner(&self) -> &MutArcInner<T> {
        unsafe { self.inner.as_ref() }
    }

    fn inner_mut(&mut self) -> &mut MutArcInner<T> {
        unsafe { self.inner.as_mut() }
    }
}

impl<T> Deref for MutArc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner().data
    }
}

impl<T> DerefMut for MutArc<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner_mut().data
    }
}

impl<T> Clone for MutArc<T> {
    fn clone(&self) -> Self {
        self.inner().ref_count.fetch_add(1, Ordering::Relaxed);
        MutArc { inner: self.inner }
    }
}

impl<T> Drop for MutArc<T> {
    fn drop(&mut self) {
        if self.inner().ref_count.fetch_sub(1, Ordering::Release) == 1 {
            unsafe {
                drop(Box::from_raw(self.inner.as_ptr()));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;

    #[test]
    fn test_basic_functionality() {
        let arc = MutArc::new(42);
        assert_eq!(*arc, 42);

        let clone = arc.clone();
        assert_eq!(*clone, 42);
    }

    #[test]
    fn test_mutation() {
        let mut arc = MutArc::new(String::from("hello"));
        arc.push_str(" world");
        assert_eq!(*arc, "hello world");

        let clone = arc.clone();
        assert_eq!(*clone, "hello world");
    }

    #[test]
    fn test_multiple_clones() {
        let arc = MutArc::new(Vec::<i32>::new());
        let clones: Vec<_> = (0..10).map(|_| arc.clone()).collect();

        for clone in clones {
            assert_eq!(*clone, Vec::<i32>::new());
        }
    }

    #[test]
    fn test_drop() {
        use std::sync::atomic::{AtomicBool, Ordering};
        use std::sync::Arc as StdArc;

        struct DropTest {
            dropped: StdArc<AtomicBool>,
        }

        impl Drop for DropTest {
            fn drop(&mut self) {
                self.dropped.store(true, Ordering::SeqCst);
            }
        }

        let dropped = StdArc::new(AtomicBool::new(false));
        let dropped_clone = dropped.clone();

        {
            let _arc = MutArc::new(DropTest {
                dropped: dropped_clone,
            });
            assert_eq!(false, dropped.load(Ordering::SeqCst));
        }

        assert_eq!(true, dropped.load(Ordering::SeqCst));
    }

    #[test]
    fn test_nested_mutation() {
        let mut arc = MutArc::new(vec![vec![1, 2], vec![3, 4]]);
        arc[0].push(5);
        arc[1].push(6);

        assert_eq!(*arc, vec![vec![1, 2, 5], vec![3, 4, 6]]);
    }

    #[test]
    fn test_large_value() {
        #[derive(Debug, PartialEq)]
        struct LargeStruct {
            data: [u8; 1024],
            counter: usize,
        }

        let large = LargeStruct {
            data: [42; 1024],
            counter: 0,
        };

        let mut arc = MutArc::new(large);
        arc.counter += 1;

        let expected = LargeStruct {
            data: [42; 1024],
            counter: 1,
        };

        assert_eq!(*arc, expected);
    }

    #[test]
    fn test_send_sync() {
        let arc = MutArc::new(42);
        let clone = arc.clone();

        thread::spawn(move || {
            assert_eq!(*clone, 42);
        })
        .join()
        .unwrap();

        let arc2 = MutArc::new(AtomicUsize::new(0));
        let clone2 = arc2.clone();

        thread::spawn(move || {
            clone2.fetch_add(1, Ordering::SeqCst);
        })
        .join()
        .unwrap();

        assert_eq!(arc2.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn test_zero_sized_type() {
        let arc = MutArc::new(());
        let clone = arc.clone();
        drop(arc);
        drop(clone);
    }
}
