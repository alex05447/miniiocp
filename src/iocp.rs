use {
    std::{
        error::Error,
        ffi::c_void,
        fmt::{Display, Formatter},
        ptr::{self, NonNull},
        time::Duration,
    },
    winapi::um::{
        handleapi::{CloseHandle, INVALID_HANDLE_VALUE},
        ioapiset::{CreateIoCompletionPort, GetQueuedCompletionStatus, PostQueuedCompletionStatus},
        minwinbase::{LPOVERLAPPED, OVERLAPPED},
        winbase::INFINITE,
        winnt::HANDLE,
    },
};

/// Describes the completed IO operation.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct IOResult {
    /// How many bytes were read/written.
    pub bytes_transferred: usize,
    /// Same value as the one provided by the caller in [`associate_handle_key`],
    /// or `0` if none was provided (by [`associate_handle`]).
    /// May be used to map back to the IO handle on which the operation was performed.
    ///
    /// NOTE: `key` value `0xffff_ffff_ffff_ffff`, a.k.a. `usize::MAX`, is reserved and will never appear here.
    ///
    /// [`associate_handle_key`]: struct.IOCP.html#method.associate_handle_key
    /// [`associate_handle`]: struct.IOCP.html#method.associate_handle
    pub key: usize,
    /// Pointer to the `OVERLAPPED` struct used for the IO operation.
    ///
    /// NOTE - this is never null, because
    /// 1) if the file was opened for asynchronous (a.k.a. overlapped) IO, a non-null `OVERLAPPED` pointer is required in `ReadFile` / `WriteFile` calls
    /// and hence will be returned when dequeueing an IO completion event off the IO completion port
    /// (even if the operation completed synchronously and the file handle was not explicitly opted out from redundant notifications
    /// (see [`SetFileCompletionNotificationModes`](https://docs.microsoft.com/en-us/windows/win32/api/winbase/nf-winbase-setfilecompletionnotificationmodes) with `FILE_SKIP_COMPLETION_PORT_ON_SUCCESS`)),
    /// 2) if the file was opened for synchronous IO, it could not have been associated with the IO completion port in the first place.
    pub overlapped: NonNull<OVERLAPPED>,
}

unsafe impl Send for IOResult {}
unsafe impl Sync for IOResult {}

/// Result of waiting on an IO completion port with a timeout.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IOCPResult {
    /// An IO operation on an associated IO handle was completed.
    ///
    /// NOTE - unless the (asynchronous) file handle was explicitly opted out
    /// (see [`SetFileCompletionNotificationModes`](https://docs.microsoft.com/en-us/windows/win32/api/winbase/nf-winbase-setfilecompletionnotificationmodes) with `FILE_SKIP_COMPLETION_PORT_ON_SUCCESS`),
    /// this might be a duplicate completion event for an IO operation that has
    /// already completed synchronously.
    IOComplete(IOResult),
    /// The port was signaled (via the call to [`IOCP::set`](struct.IOCP.html#method.set)).
    Signaled,
    /// The timeout duration in the call to [`IOCP::wait`](struct.IOCP.html#method.wait) elapsed
    /// before an IO operation was completed / the port was signaled.
    Timeout,
}

#[derive(Debug)]
pub enum IOCPError {
    /// Failed to create the IO completion port.
    FailedToCreate,
    /// Key value `usize::MAX` is reserved.
    InvalidKey,
    /// Tried to associate an invalid handle with the IO completion port.
    InvalidIOHandle,
    /// Failed to associate the IO handle with the IO completion port
    /// (e.g., the handle was not opened for overlapped IO).
    /// Contains the OS error.
    FailedToAssociate(std::io::Error),
    /// Failed to wait on the IO completion port.
    /// Contains the OS error.
    FailedToWait(std::io::Error),
}

impl Error for IOCPError {}

impl Display for IOCPError {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        use IOCPError::*;

        match self {
            FailedToCreate => "failed to create the IO completion port".fmt(f),
            InvalidKey => "key value `usize::MAX` is reserved".fmt(f),
            InvalidIOHandle => {
                "tried to associate an invalid handle with the IO completion port".fmt(f)
            }
            FailedToAssociate(err) => write!(
                f,
                "failed to associate the IO handle with the IO completion port: {}",
                err
            ),
            FailedToWait(err) => write!(f, "failed to wait on the IO completion port: {}", err),
        }
    }
}

/// The object that represents a Windows IO completion port.
///
/// Closes the owned OS handle when dropped.
///
/// See [`the I/O Completion Ports documentation`](https://docs.microsoft.com/en-us/windows/win32/fileio/i-o-completion-ports) for more information.
pub struct IOCP {
    handle: NonNull<c_void>,
}

unsafe impl Send for IOCP {}
unsafe impl Sync for IOCP {}

const IOCP_SIGNALED_KEY: usize = usize::MAX;

impl IOCP {
    /// Creates a new IO completion port on which up to `num_threads` may block
    /// waiting for async IO operations to complete.
    /// `1` is a good default value.
    /// `0` means the OS will allow as many threads as system cores to block.
    ///
    /// May return an error if the OS IO completion object creation failed for some reason.
    pub fn new(num_threads: usize) -> Result<Self, IOCPError> {
        let handle =
            unsafe { CreateIoCompletionPort(INVALID_HANDLE_VALUE, 0 as _, 0, num_threads as _) };

        let handle = NonNull::new(handle).ok_or(IOCPError::FailedToCreate)?;

        Ok(Self { handle })
    }

    /// Associates the `io_handle` (opened for async a.k.a "overlapped" IO) with the IO completion port.
    ///
    /// The IOCP will be notified when an async IO operation completes for this `io_handle`, waking one thread
    /// from the call to [`wait`] / [`wait_infinite`] with [`IOCPResult::IOComplete`].
    ///
    /// Returns an error if the `io_handle` is invalid or was not opened for overlapped IO.
    ///
    /// # Remarks
    ///
    /// Unless the IO handle has explicitly opted out
    /// (see [`SetFileCompletionNotificationModes`](https://docs.microsoft.com/en-us/windows/win32/api/winbase/nf-winbase-setfilecompletionnotificationmodes)
    /// with `FILE_SKIP_COMPLETION_PORT_ON_SUCCESS`),
    /// the IOCP will also be notified if the IO operation has completed synchronously for this `io_handle`,
    /// which might cause the completion to be handled twice and lead to bugs.
    ///
    /// [`wait`]: #method.wait
    /// [`wait_infinite`]: #method.wait_infinite
    /// [`IOCPResult::IOComplete`]: enum.IOCPResult.html#variant.IOComplete
    pub fn associate_handle(&self, io_handle: HANDLE) -> Result<(), IOCPError> {
        self.associate_handle_impl(io_handle, 0)
    }

    /// Associates the `io_handle` (open for async a.k.a "overlapped" IO) with the IO completion port.
    ///
    /// The IOCP will be notified when an async IO operation completes for this `io_handle`, waking one thread
    /// from the call to [`wait`] / [`wait_infinite`] with [`IOCPResult::IOComplete`].
    ///
    /// Provided user-defined `key` will be returned in [`IOResult`](struct.IOResult.html#field.key)
    /// on IO completion.
    ///
    /// NOTE: `key` value `0xffff_ffff_ffff_ffff`, a.k.a. `usize::MAX`, is reserved.
    ///
    /// Returns an error if the `io_handle` is invalid, was not opened for overlapped IO, or if `key` is `usize::MAX`.
    ///
    /// # Remarks
    ///
    /// Unless the IO handle has explicitly opted out
    /// (see [`SetFileCompletionNotificationModes`](https://docs.microsoft.com/en-us/windows/win32/api/winbase/nf-winbase-setfilecompletionnotificationmodes)
    /// with `FILE_SKIP_COMPLETION_PORT_ON_SUCCESS`),
    /// the IOCP will also be notified if the IO operation has completed synchronously for this `io_handle`,
    /// which might cause the completion to be handled twice and lead to bugs.
    ///
    /// [`wait`]: #method.wait
    /// [`wait_infinite`]: #method.wait_infinite
    /// [`IOCPResult::IOComplete`]: enum.IOCPResult.html#variant.IOComplete
    pub fn associate_handle_key(&self, io_handle: HANDLE, key: usize) -> Result<(), IOCPError> {
        self.associate_handle_impl(io_handle, key)
    }

    /// Wakes up one thread blocked on the call to [`wait`] / [`wait_infinite`] with [`IOCPResult::Signaled`].
    ///
    /// [`wait`]: #method.wait
    /// [`wait_infinite`]: #method.wait_infinite
    /// [`IOCPResult::Signaled`]: enum.IOCPResult.html#variant.Signaled
    pub fn set(&self) {
        let result = unsafe {
            PostQueuedCompletionStatus(
                self.handle.as_ptr(),
                0,
                IOCP_SIGNALED_KEY,
                ptr::null_mut() as _,
            )
        };

        debug_assert!(result != 0);
    }

    /// Blocks the current thread until
    /// 1) an async IO operation completes on one of the IO handles associated with the IO completion port
    /// (via the call to [`associate_handle`] / [`associate_handle_key`]),
    /// 2) the IO completion port is signaled
    /// (via the call to [`set`]),
    /// 3) the timeout `d` elapses.
    /// Returns the corresponding variant of [`IOCPResult`].
    ///
    /// [`associate_handle`]: #method.associate_handle
    /// [`associate_handle_key`]: #method.associate_handle_key
    /// [`set`]: #method.set
    /// [`IOCPResult`]: enum.IOCPResult.html
    pub fn wait(&self, d: Duration) -> Result<IOCPResult, IOCPError> {
        let ms = d.as_millis();
        debug_assert!(ms <= std::u32::MAX as u128);
        let ms = ms as u32;

        self.wait_impl(ms)
    }

    /// Blocks the current thread until
    /// 1) an async IO operation completes on one of the IO handles associated with the IO completion port
    /// (via the call to [`associate_handle`] / [`associate_handle_key`]),
    /// 2) the IO completion port is signaled
    /// (via the call to [`set`]),
    /// Returns the corresponding variant of [`IOCPResult`] (except [`Timeout`]).
    ///
    /// [`associate_handle`]: #method.associate_handle
    /// [`associate_handle_key`]: #method.associate_handle_key
    /// [`set`]: #method.set
    /// [`IOCPResult`]: enum.IOCPResult.html
    /// [`Timeout`]: enum.IOCPResult.html#variant.Timeout
    pub fn wait_infinite(&self) -> Result<IOCPResult, IOCPError> {
        self.wait_impl(INFINITE)
    }

    fn associate_handle_impl(&self, io_handle: HANDLE, key: usize) -> Result<(), IOCPError> {
        if (io_handle == INVALID_HANDLE_VALUE) || (io_handle == 0 as _) {
            return Err(IOCPError::InvalidIOHandle);
        }

        if key == IOCP_SIGNALED_KEY {
            return Err(IOCPError::InvalidKey);
        }

        let handle = unsafe { CreateIoCompletionPort(io_handle, self.handle.as_ptr(), key, 0) };

        if handle == self.handle.as_ptr() {
            Ok(())
        } else {
            Err(IOCPError::FailedToAssociate(std::io::Error::last_os_error()))
        }
    }

    fn wait_impl(&self, ms: u32) -> Result<IOCPResult, IOCPError> {
        let mut key: usize = 0;

        let mut bytes_transferred: u32 = 0;
        let mut overlapped: LPOVERLAPPED = ptr::null_mut();

        let result = unsafe {
            GetQueuedCompletionStatus(
                self.handle.as_ptr(),
                &mut bytes_transferred as *mut _,
                &mut key as *mut _,
                &mut overlapped as *mut _,
                ms,
            )
        };

        // Success.
        if result != 0 {
            // If dequeued a signal event.
            if key == IOCP_SIGNALED_KEY {
                debug_assert!(overlapped.is_null());
                debug_assert!(bytes_transferred == 0);

                return Ok(IOCPResult::Signaled);
            }
            // Dequeued an IO completion event.
            else {
                debug_assert!(!overlapped.is_null());

                return Ok(IOCPResult::IOComplete(IOResult {
                    bytes_transferred: bytes_transferred as usize,
                    key,
                    overlapped: unsafe { NonNull::new_unchecked(overlapped) },
                }));
            }

        // Failure.
        } else {
            // Timeout.
            if (ms != INFINITE) && overlapped.is_null() {
                return Ok(IOCPResult::Timeout);
            }

            // Unknown error otherwise.
            // NOTE: includes successful dequeueing of failed IO. Might want to handle this properly in the future.
            Err(IOCPError::FailedToWait(std::io::Error::last_os_error()))
        }
    }
}

impl Drop for IOCP {
    fn drop(&mut self) {
        unsafe {
            CloseHandle(self.handle.as_ptr());
        }
    }
}

#[cfg(test)]
mod tests {
    #![allow(non_snake_case)]

    use std::{
        cmp, fs, io, mem,
        os::windows::{fs::OpenOptionsExt, io::AsRawHandle},
        path::Path,
        sync::{
            atomic::{AtomicBool, AtomicUsize, Ordering},
            Arc,
        },
        thread,
        time::Instant,
    };

    use winapi::{
        shared::{minwindef::DWORD, winerror::ERROR_IO_PENDING},
        um::{
            errhandlingapi::GetLastError,
            fileapi::WriteFile,
            ioapiset::GetOverlappedResult,
            minwinbase::OVERLAPPED,
            winbase::{
                SetFileCompletionNotificationModes, FILE_FLAG_OVERLAPPED,
                FILE_SKIP_COMPLETION_PORT_ON_SUCCESS, FILE_SKIP_SET_EVENT_ON_HANDLE,
            },
        },
    };

    use super::*;

    #[test]
    fn iocp_set() {
        // This is how many threads may block on an IOCP - we'll use two threads for the test.
        let num_threads = 2;

        // It's simpler to just use `Arc` here, but it's OK to pass references / pointers to the IOCP to other threads
        // (it's `Send` and `Sync`) - just make sure it's only dropped once.
        let iocp = Arc::new(IOCP::new(num_threads).unwrap()); // Not signaled.

        // Create two threads which will just wait for the IOCP for a (very long) duration.
        // They'll wake up only when we signal the IOCP explicitly, as we won't perform any IO here.
        let iocp_1 = iocp.clone();
        let t_1 = thread::spawn(move || {
            let now = Instant::now();
            let res = iocp_1.wait(Duration::from_secs(1_000_000)).unwrap();
            let elapsed = now.elapsed();
            (res, elapsed)
        });

        let iocp_2 = iocp.clone();
        let t_2 = thread::spawn(move || {
            let now = Instant::now();
            let res = iocp_2.wait(Duration::from_secs(1_000_000)).unwrap();
            let elapsed = now.elapsed();
            (res, elapsed)
        });

        // Wait for a second.
        thread::sleep(Duration::from_secs(1));

        // Signal one (random) thread.
        iocp.set();

        // One of the threads has exited, the other is still waiting.

        // Wait for another second.
        thread::sleep(Duration::from_millis(1_000));

        iocp.set();

        // Now both must have exited.

        let (res_1, elapsed_1) = t_1.join().unwrap();

        assert!(matches!(res_1, IOCPResult::Signaled));
        assert!(elapsed_1.as_millis() >= 500); // We waited for at least a second before a thread got signaled and exited.

        let (res_2, elapsed_2) = t_2.join().unwrap();

        assert!(matches!(res_2, IOCPResult::Signaled));
        assert!(elapsed_2.as_millis() >= 500); // We waited for at least a second before a thread got signaled and exited.

        // Find out which one of the threads exited first, and which one - a second later.
        if elapsed_1.as_millis() > elapsed_2.as_millis() {
            assert!(elapsed_1.as_millis() - elapsed_2.as_millis() >= 500); // We waited for at least a second before the second thread got signaled and exited.
        } else {
            assert!(elapsed_2.as_millis() - elapsed_1.as_millis() >= 500); // We waited for at least a second before the second thread got signaled and exited.
        }

        // The IOCP is now not signaled again - we must time out if we block on it.

        let res = iocp.wait(Duration::from_millis(1)).unwrap();
        assert!(matches!(res, IOCPResult::Timeout));
    }

    #[test]
    fn IOCPError_InvalidIOHandle() {
        let iocp = Arc::new(IOCP::new(1).unwrap()); // Not signaled.

        assert!(matches!(
            iocp.associate_handle(0 as _).err().unwrap(),
            IOCPError::InvalidIOHandle
        ));
        assert!(matches!(
            iocp.associate_handle_key(0 as _, 0).err().unwrap(),
            IOCPError::InvalidIOHandle
        ));
    }

    #[test]
    fn IOCPError_FailedToAssociate() {
        let iocp = Arc::new(IOCP::new(1).unwrap()); // Not signaled.

        let file_name = "test.txt";

        // The file is not open for async IO.
        let file = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(file_name)
            .unwrap();

        assert!(matches!(
            iocp.associate_handle(file.as_raw_handle()).err().unwrap(),
            IOCPError::FailedToAssociate(_)
        ));
        assert!(matches!(
            iocp.associate_handle_key(file.as_raw_handle(), 0)
                .err()
                .unwrap(),
            IOCPError::FailedToAssociate(_)
        ));

        fs::remove_file(file_name).unwrap();
    }

    #[test]
    fn async_write() {
        // Opens the file for async IO.
        // Uses `std::fs::OpenOptions` Windows-specific extension.
        fn open_async_file<P: AsRef<Path>>(path: P) -> fs::File {
            let file = fs::OpenOptions::new()
                .create(true)
                .append(true)
                .custom_flags(FILE_FLAG_OVERLAPPED) // <- this is the async IO flag
                .open(path)
                .unwrap();

            // Important - we do not want to notify the IOCP if the operation actually completed synchronously.
            // Also do not signal the file handle on completion.
            let result = unsafe {
                SetFileCompletionNotificationModes(
                    file.as_raw_handle(),
                    FILE_SKIP_COMPLETION_PORT_ON_SUCCESS | FILE_SKIP_SET_EVENT_ON_HANDLE,
                )
            };
            assert!(result > 0);

            file
        }
        enum WriteFileAsyncResult {
            /// Write completed synchronously.
            /// Contains the number of bytes written.
            Sync(usize),
            /// Write completed asynchronously.
            /// IOCP will be notified of actual write completion later.
            Async,
        }

        /// Tries to write the data in `buf` to the file `handle`.
        /// NOTE - `handle` must be opened for async IO.
        fn write_file_async(
            handle: HANDLE,
            overlapped: NonNull<OVERLAPPED>,
            buf: &[u8],
        ) -> io::Result<WriteFileAsyncResult> {
            let len = cmp::min(buf.len(), DWORD::MAX as usize) as DWORD;

            let mut written: DWORD = 0;

            let result = unsafe {
                WriteFile(
                    handle,
                    buf.as_ptr() as _,
                    len,
                    &mut written,
                    overlapped.as_ptr(),
                )
            };

            // The write completed synchronously.
            if result != 0 {
                return Ok(WriteFileAsyncResult::Sync(written as usize));

            // Else the write either completed synchronously or there was an error.
            } else {
                let error = unsafe { GetLastError() };

                // Completed asynchronously.
                if error == ERROR_IO_PENDING {
                    return Ok(WriteFileAsyncResult::Async);

                // Some actual error.
                } else {
                    return Err(io::Error::from_raw_os_error(error as _));
                }
            }
        }

        /// `num_pending` will be decremented by the calling thread here if the file write completes synchronously,
        /// but is not used if the file write is initiated asyncronously.
        /// `completion_flag` will be set by the main thread when the file write which was initiated asyncronously
        /// completes (as signaled by the IOCP).
        /// I.e., `completion_flag` will not be used at all if the file write was completed synchronously.
        fn do_the_thing<P: AsRef<Path>>(
            iocp: &IOCP,
            path: P,
            key: usize,
            buf: &[u8],
            num_pending: &AtomicUsize,
            completion_flag: &AtomicBool,
        ) {
            // Open the file for async IO and associate it with the IOCP.
            let file = open_async_file(path);
            iocp.associate_handle_key(file.as_raw_handle(), key)
                .unwrap();

            // Issue the write, passing the pointer to the `OVERLAPPED` struct on the stack.
            // NOTE - the `OVERLAPPED` struct must not go out of scope until the write actually completes.
            let mut overlapped: OVERLAPPED = unsafe { mem::zeroed() };
            let res = write_file_async(
                file.as_raw_handle(),
                unsafe { NonNull::new_unchecked(&mut overlapped) },
                buf,
            )
            .unwrap();

            match res {
                // The write completed synchronously.
                WriteFileAsyncResult::Sync(bytes_transferred) => {
                    assert_eq!(bytes_transferred, buf.len());
                    // Decrement the pending counter for the main thread.
                    num_pending.fetch_sub(1, Ordering::SeqCst);
                }
                // The write completed asynchronously.
                WriteFileAsyncResult::Async => {
                    // Wait for actual IO completion as signaled by the IOCP in the main thread.
                    // We could use an event in the `OVERLAPPED` struct, or some other waitable event, but I'm too lazy.
                    while !completion_flag.load(Ordering::SeqCst) {
                        thread::yield_now();
                    }
                    // IOCP was notified of IO completion with this thread's key, and the main thread set the `completion_flag`
                    // for the correct thread.

                    // Get the number of bytes transferred using the same `OVERLAPPED` pointer we passed to `WriteFile` -
                    // this is why the `OVERLAPPED` struct must live until this point.
                    let mut bytes_transferred: DWORD = 0;

                    let result = unsafe {
                        GetOverlappedResult(
                            file.as_raw_handle(),
                            &mut overlapped,
                            &mut bytes_transferred,
                            false as _, // <- we don't need to wait on an `OVERLAPPED` event / file handle as we know the operation has completed via IOCP.
                        )
                    };

                    assert!(result > 0);
                    assert_eq!(bytes_transferred as usize, buf.len());

                    // Main thread has already handled the pending counter.
                }
            }
        }

        // We'll use one thread (the main thread) in this test to wait on the IOCP.
        let num_threads = 1;

        // It's simpler to just use `Arc` here, but it's OK to pass references / pointers to the IOCP to other threads
        // (it's `Send` and `Sync`) - just make sure it's only dropped once.
        let iocp = Arc::new(IOCP::new(num_threads).unwrap());

        // We'll issue 2 file writes.
        let num_pending = 2;
        let num_pending = Arc::new(AtomicUsize::new(num_pending));

        let file_name = "test.txt";

        // We'll spawn two threads to actually open the file and perform the writes.

        // Thread 1 will write this data with this key.
        let thread_1_key = 1;
        let thread_1_data = b"1111";
        let thread_1_flag = Arc::new(AtomicBool::new(false));

        // Thread 2 will write this data with this key.
        let thread_2_key = 2;
        let thread_2_data = b"22222222";
        let thread_2_flag = Arc::new(AtomicBool::new(false));

        // Sapwn the threads.

        let iocp_1 = iocp.clone();
        let num_pending_1 = num_pending.clone();
        let thread_1_flag_clone = thread_1_flag.clone();
        let t_1 = thread::spawn(move || {
            do_the_thing(
                &iocp_1,
                file_name,
                thread_1_key,
                thread_1_data,
                &num_pending_1,
                &thread_1_flag_clone,
            );
        });

        let iocp_2 = iocp.clone();
        let num_pending_2 = num_pending.clone();
        let thread_2_flag_clone = thread_2_flag.clone();
        let t_2 = thread::spawn(move || {
            do_the_thing(
                &iocp_2,
                file_name,
                thread_2_key,
                thread_2_data,
                &num_pending_2,
                &thread_2_flag_clone,
            );
        });

        // The main thread will wait for all write operations to either
        // 1) complete synchronously (worker threads will then decrement `num_pending` and exit), or
        // 2) complete asynchronously (then we'll "wake" the correct thread via its `completion_flag`)
        // and handle the `num_pending` counter ourselves.
        while num_pending.load(Ordering::SeqCst) > 0 {
            // Blocking wait on the IOCP.
            let result = iocp.wait_infinite().unwrap();
            // The IOCP has woken us up.

            match result {
                // IO completion is the only expected outcome.
                IOCPResult::IOComplete(ioresult) => {
                    // The `key` in the async IO result allows us to figure out which thread's file write
                    // has completed.
                    match ioresult.key {
                        // Thread 1 async IO completed.
                        1 => {
                            assert_eq!(ioresult.bytes_transferred, thread_1_data.len());
                            num_pending.fetch_sub(1, Ordering::SeqCst);

                            // "Wake" the thread and let it exit.
                            thread_1_flag.store(true, Ordering::SeqCst);
                        }
                        // Thread 2 async IO completed.
                        2 => {
                            assert_eq!(ioresult.bytes_transferred, thread_2_data.len());
                            num_pending.fetch_sub(1, Ordering::SeqCst);

                            // "Wake" the thread and let it exit.
                            thread_2_flag.store(true, Ordering::SeqCst);
                        }
                        _ => {
                            unreachable!();
                        }
                    }
                }
                _ => {
                    panic!("expected IO completion");
                }
            }
        }

        // All file writes have completed, both worker threads are free to exit - wait for them to do so.

        t_2.join().unwrap();
        t_1.join().unwrap();

        // Open the file for reading and make sure it's the correct length at least.
        // There's no easy way to guarantee file contents when writen to from multiple threads
        // as writes are generally speaking non-atomic (although they *can* be).
        let read_file = fs::File::open(file_name).unwrap();
        let metadata = read_file.metadata().unwrap();
        let len = metadata.len();

        assert_eq!(len, (thread_1_data.len() + thread_2_data.len()) as _);

        // Clean up the temporary file.
        fs::remove_file(file_name).unwrap();
    }
}
