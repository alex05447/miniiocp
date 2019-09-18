//! Thin wrapper around the Windows IO completion port.
//! See [`I/O Completion Ports`](https://docs.microsoft.com/en-us/windows/win32/fileio/i-o-completion-ports).

mod iocp;

pub use crate::iocp::{ IOResult, IOCPResult, IOCP };