//! Thin wrapper around the Windows IO completion port.
//!
//! See [`I/O Completion Ports`](https://docs.microsoft.com/en-us/windows/win32/fileio/i-o-completion-ports) on MSDN for the description of the concept.
//!
//! Run `cargo --doc` for documentation.
//!
//! Uses [`winapi`](https://docs.rs/winapi/0.3.8/winapi/).

mod iocp;

pub use crate::iocp::{ IOResult, IOCPResult, IOCP };