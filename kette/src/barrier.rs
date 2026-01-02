use std::sync::{Condvar, Mutex};

/// A reusable synchronization barrier that puts threads to sleep
#[derive(Debug, Default)]
pub struct SenseBarrier {
    /// Protected state: (current_count, current_sense)
    state: Mutex<(usize, bool)>,
    cvar: Condvar,
}

impl SenseBarrier {
    pub fn new() -> Self {
        Self {
            state: Mutex::new((0, false)),
            cvar: Condvar::new(),
        }
    }

    /// Blocks the current thread until `until` have called this function.
    pub fn wait(&self, until: usize) {
        let mut state = self.state.lock().expect("TODO: handle poison");

        let my_sense = state.1;

        state.0 += 1;

        if state.0 == until {
            // LAST
            state.0 = 0;
            state.1 = !my_sense;

            self.cvar.notify_all();
        } else {
            // FOLLOWER
            while state.1 == my_sense {
                state = self.cvar.wait(state).expect("TODO: handle poison");
            }
        }
    }
}
