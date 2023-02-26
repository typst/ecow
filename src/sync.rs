/// Loom needs its own syncronization types to be used in order to work
pub mod atomic {
    #[cfg(not(loom))]
    pub use core::sync::atomic::*;

    #[cfg(loom)]
    pub use loom::sync::atomic::*;
}
