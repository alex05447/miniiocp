use std::ptr;
use std::time::Duration;

use winapi::um::winnt::HANDLE;
use winapi::um::winbase::INFINITE;
use winapi::um::ioapiset::{ CreateIoCompletionPort, GetQueuedCompletionStatus, PostQueuedCompletionStatus };
use winapi::um::handleapi::{ INVALID_HANDLE_VALUE, CloseHandle };
use winapi::um::minwinbase::{ OVERLAPPED, LPOVERLAPPED };
use winapi::um::errhandlingapi::GetLastError;

/// Describes the completed async IO operation.
pub struct IOResult {
    /// How many bytes were read/written.
    pub bytes_transferred :usize,

    /// Same value as the one provided by the caller in [`associate_handle_key`],
    /// or `0` if none was provided (by [`associate_handle`]).
    /// May be used to map back to the IO handle on which the operation was performed.
    ///
    /// [`associate_handle_key`]: struct.IOCP.html#method.associate_handle_key
    /// [`associate_handle`]: struct.IOCP.html#method.associate_handle
    pub key :usize,

    /// Pointer to the `OVERLAPPED` struct used for the IO operation.
    pub overlapped :*const OVERLAPPED,
}

unsafe impl Send for IOResult {}
unsafe impl Sync for IOResult {}

/// Result of waiting on an IO completion port with a timeout.
pub enum IOCPResult {
    /// An IO operation on an associated IO handle was completed.
    IOComplete(IOResult),

    /// The port was signaled (via the call to [`IOCP::set`](struct.IOCP.html#method.set)).
    Signaled,

    /// The timeout duration elapsed before an IO operation was completed / the port was signaled.
    Timeout,
}

/// The object that represents a Windows IO completion port.
/// Closes the owned OS handle when dropped.
/// See [`I/O Completion Ports`](https://docs.microsoft.com/en-us/windows/win32/fileio/i-o-completion-ports).
pub struct IOCP {
    handle :HANDLE,
}

unsafe impl Send for IOCP {}
unsafe impl Sync for IOCP {}

const IOCP_SIGNALED_KEY :usize = 0xffff_ffff;

impl IOCP {
    /// Creates a new IO completion port on which up to `num_threads` may block
    /// waiting for async IO operations to complete.
    /// `1` is a good default value.
    /// `0` means the OS will allow as many threads as system cores to block.
    ///
    /// # Panics
    ///
    /// Panics if the OS object creation fails.
    pub fn new(num_threads :usize) -> Self {
        let handle = unsafe {
            CreateIoCompletionPort(
                INVALID_HANDLE_VALUE
                ,0 as HANDLE
                ,0
                ,num_threads as _
            )
        };

        if handle.is_null() {
            panic!("IO completion port creation failed.");
        }

        Self {
            handle
        }
    }

    /// Associates the `io_handle` (open for async a.k.a "overlapped" IO) with the IO completion port.
    /// The IOCP will be notified when the async IO operation completes, waking one thread
    /// from the call to [`wait`] / [`wait_infinite`] with [`IOCPResult::IOComplete`].
    ///
    /// # Remarks
    ///
    /// Unless the IO handle has explicitly opted out
    /// (see [`SetFileCompletionNotificationModes`](https://docs.microsoft.com/en-us/windows/win32/api/winbase/nf-winbase-setfilecompletionnotificationmodes)
    /// with `FILE_SKIP_COMPLETION_PORT_ON_SUCCESS`),
    /// the IOCP will also be notified if the IO operation has completed synchronously,
    /// which might cause the completion to be handled twice and lead to bugs.
    ///
    /// [`wait`]: #method.wait
    /// [`wait_infinite`]: #method.wait_infinite
    /// [`IOCPResult::IOComplete`]: enum.IOCPResult.html#variant.IOComplete
    pub fn associate_handle(&self, io_handle :HANDLE) {
        self.associate_handle_impl(io_handle, 0)
    }

    /// Associates the `io_handle` (open for async a.k.a "overlapped" IO) with the IO completion port.
    /// The IOCP will be notified when the async IO operation completes, waking one thread
    /// from the call to [`wait`] / [`wait_infinite`] with [`IOCPResult::IOComplete`].
    ///
    /// Provided user-defined `key` will be returned in [`IOResult`](struct.IOResult.html#field.key)
    /// on IO completion.
    ///
    /// `key` value `0xffff_ffff` is reserved.
    ///
    /// # Remarks
    ///
    /// Unless the IO handle has explicitly opted out
    /// (see [`SetFileCompletionNotificationModes`](https://docs.microsoft.com/en-us/windows/win32/api/winbase/nf-winbase-setfilecompletionnotificationmodes)
    /// with `FILE_SKIP_COMPLETION_PORT_ON_SUCCESS`),
    /// the IOCP will also be notified if the IO operation has completed synchronously,
    /// which might cause the completion to be handled twice and lead to bugs.
    ///
    /// # Pancis
    ///
    /// Panics if the invalid `key` value (`0xffff_ffff`) was provided.
    ///
    /// [`wait`]: #method.wait
    /// [`wait_infinite`]: #method.wait_infinite
    /// [`IOCPResult::IOComplete`]: enum.IOCPResult.html#variant.IOComplete
    pub fn associate_handle_key(&self, io_handle :HANDLE, key :usize) {
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
                self.handle
                ,0
                ,IOCP_SIGNALED_KEY
                ,ptr::null_mut() as _
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
    pub fn wait(&self, d :Duration) -> IOCPResult {
        let ms = d.as_millis();
        debug_assert!(ms <= std::u32::MAX as u128);
        let ms = ms as u32;

        self.wait_internal(ms)
    }

    /// Blocks the current thread until
    /// 1) an async IO operation completes on one of the IO handles associated with the IO completion port
    /// (via the call to [`associate_handle`] / [`associate_handle_key`]),
    /// 2) the IO completion port is signaled
    /// (via the call to [`set`]),
    /// Returns the corresponding variant of [`IOCPResult`] (except `IOCPResult::Timeout`).
    ///
    /// [`associate_handle`]: #method.associate_handle
    /// [`associate_handle_key`]: #method.associate_handle_key
    /// [`set`]: #method.set
    /// [`IOCPResult`]: enum.IOCPResult.html
    pub fn wait_infinite(&self) -> IOCPResult {
        self.wait_internal(INFINITE)
    }

    fn associate_handle_impl(&self, io_handle :HANDLE, key :usize) {
        debug_assert!(io_handle != INVALID_HANDLE_VALUE);
        debug_assert!(io_handle != 0 as HANDLE);

        assert!(key != IOCP_SIGNALED_KEY, "Key value `0xffff_ffff` is reserved for internal use.");

        let handle = unsafe {
            CreateIoCompletionPort(
                io_handle
                ,self.handle
                ,key
                ,1
            )
        };

        if handle != self.handle {
            panic!("Failed to associate the handle with the IOCompletionPort.");
        }
    }

    fn wait_internal(&self, ms :u32) -> IOCPResult {
        let mut key :usize = 0;

        let mut bytes_transferred :u32 = 0;
        let mut overlapped :LPOVERLAPPED = ptr::null_mut();

        let result = unsafe {
            GetQueuedCompletionStatus(
                self.handle
                ,&mut bytes_transferred as *mut _
                ,&mut key as *mut _
                ,&mut overlapped as *mut _
                ,ms
            )
        };

        // Success.
        if result != 0 {
            // If dequeued a signal event.
            if key == IOCP_SIGNALED_KEY {
                debug_assert!(overlapped.is_null());
                debug_assert!(bytes_transferred == 0);

                return IOCPResult::Signaled;
            }

            // Dequeued an IO completion event.
            else {
                debug_assert!(!overlapped.is_null());

                return IOCPResult::IOComplete(
                    IOResult {
                        bytes_transferred : bytes_transferred as usize, key, overlapped
                    }
                );
            }

        // Failure.
        } else {
            // Timeout.
            if (ms != INFINITE) && overlapped.is_null() {
                return IOCPResult::Timeout;
            }

            // Unknown error otherwise.
            // NOTE: includes successful dequeueing of failed IO. Might want to handle this properly in the future.
            let error = unsafe {
                GetLastError()
            };

            panic!("Unknown error (code `{}`) when waiting on IOCompletionPort.", error);
        }
    }
}

impl Drop for IOCP {
    fn drop(&mut self) {
        unsafe {
            CloseHandle(self.handle);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{
        cmp
        ,io
        ,mem
        ,path::Path
        ,sync::{ Arc, atomic::{ AtomicUsize, AtomicBool, Ordering } }
        ,thread
        ,time::Instant
        ,mem::discriminant
        ,fs
        ,os::windows::{ fs::OpenOptionsExt, io::AsRawHandle }
    };

    use winapi::shared::minwindef::DWORD;
    use winapi::shared::winerror::ERROR_IO_PENDING;
    use winapi::um::minwinbase::OVERLAPPED;
    use winapi::um::winbase::{ FILE_FLAG_OVERLAPPED, SetFileCompletionNotificationModes, FILE_SKIP_COMPLETION_PORT_ON_SUCCESS, FILE_SKIP_SET_EVENT_ON_HANDLE };
    use winapi::um::fileapi::WriteFile;
    use winapi::um::errhandlingapi::GetLastError;
    use winapi::um::ioapiset::GetOverlappedResult;

    use super::*;

    #[test]
    fn iocp_thread_signal() {
        let num_threads = 2;
        let iocp = Arc::new(IOCP::new(num_threads)); // Not signaled.

        let iocp_1 = iocp.clone();
        let t_1 = thread::spawn(move || {
            let now = Instant::now();
            let res = iocp_1.wait(Duration::from_secs(1_000_000));
            let elapsed = now.elapsed();
            (res, elapsed)
        });

        let iocp_2 = iocp.clone();
        let t_2 = thread::spawn(move|| {
            let now = Instant::now();
            let res = iocp_2.wait(Duration::from_secs(1_000_000));
            let elapsed = now.elapsed();
            (res, elapsed)
        });

        // Wait for a second.
        thread::sleep(Duration::from_secs(1));

        iocp.set();

        // One of the threads has exited, the other is still waiting.

        thread::sleep(Duration::from_millis(1_000));

        iocp.set();

        // Now both have exited.

        let res_1 = t_1.join().unwrap();

        assert!(discriminant(&res_1.0) == discriminant(&IOCPResult::Signaled));
        assert!(res_1.1.as_millis() >= 500);

        let res_2 = t_2.join().unwrap();

        assert!(discriminant(&res_2.0) == discriminant(&IOCPResult::Signaled));
        assert!(res_2.1.as_millis() >= 500);

        if res_1.1.as_millis() > res_2.1.as_millis() {
            assert!( res_1.1.as_millis() - res_2.1.as_millis() >= 500 );
        } else {
            assert!( res_2.1.as_millis() - res_1.1.as_millis() >= 500 );
        }

        // Not signaled.

        let res = iocp.wait(Duration::from_millis(1));
        assert!(discriminant(&res) == discriminant(&IOCPResult::Timeout));
    }

    #[test]
    fn file_write() {
        // Opens the file for async IO.
        // Uses `std::fs::OpenOptions` Windows extension.
        fn open_async_file<P: AsRef<Path>>(path: P) -> fs::File {
            let file = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .custom_flags(FILE_FLAG_OVERLAPPED)
            .open(path)
            .unwrap();

            // Do not notify the IOCP if the operation actually completed synchronously
            // (e.g., the file was opened for sync IO).
            // Also do not set the file handle / explicit event in `OVERLAPPED` on completion.
            let result = unsafe {
                SetFileCompletionNotificationModes(file.as_raw_handle(), FILE_SKIP_COMPLETION_PORT_ON_SUCCESS | FILE_SKIP_SET_EVENT_ON_HANDLE)
            };
            assert!(result > 0);

            file
        }

        enum WriteToAsyncFileResult {
            Sync(usize),
            Async,
        }

        fn write_to_async_file(handle :HANDLE, overlapped :*mut OVERLAPPED, buf :&[u8]) -> io::Result<WriteToAsyncFileResult> {
            let len = cmp::min(buf.len(), <DWORD>::max_value() as usize) as DWORD;

            let mut written :DWORD = 0;

            let result = unsafe {
                WriteFile(
                    handle
                    ,buf.as_ptr() as _
                    ,len
                    ,&mut written
                    ,overlapped
                )
            };

            // The write completed synchronously.
            if result != 0 {
                return Ok(WriteToAsyncFileResult::Sync(written as usize));

            } else {
                let error = unsafe { GetLastError() };

                // Completed asynchronously.
                if error == ERROR_IO_PENDING {
                    return Ok(WriteToAsyncFileResult::Async);

                // Some actual error.
                } else {
                    return Err(io::Error::from_raw_os_error(error as i32));
                }
            }
        }

        fn do_the_thing<P: AsRef<Path>>(iocp :&IOCP, path: P, key :usize, buf :&[u8], num_pending :&AtomicUsize, completion_flag :&AtomicBool) {
            let file = open_async_file(path);

            iocp.associate_handle_key(file.as_raw_handle(), key);

            let mut overlapped :OVERLAPPED = unsafe { mem::zeroed() };
            let res = write_to_async_file(file.as_raw_handle(), &mut overlapped, buf);

            match res {
                Ok(WriteToAsyncFileResult::Sync(bytes_transferred)) => {
                    assert_eq!(bytes_transferred, buf.len());
                    num_pending.fetch_sub(1, Ordering::SeqCst);
                },
                Ok(WriteToAsyncFileResult::Async) => {
                    // Or we could use an event in the `OVERLAPPED`, but I'm too lazy.
                    while !completion_flag.load(Ordering::SeqCst) {
                        thread::yield_now();
                    }

                    let mut bytes_transferred :DWORD = 0;

                    let result = unsafe {
                        GetOverlappedResult(
                            file.as_raw_handle()
                            ,&mut overlapped
                            ,&mut bytes_transferred
                            ,false as _
                        )
                    };

                    assert!(result > 0);
                    assert_eq!(bytes_transferred as usize, buf.len());
                },
                Err(_) => panic!("Write to async file failed."),
            }
        }

        let num_threads = 1;
        let iocp = Arc::new(IOCP::new(num_threads)); // Not signaled.

        let num_pending = Arc::new(AtomicUsize::new(2));

        let file_name = "test.txt";

        let thread_1_key = 1;
        let thread_1_data = b"1111";
        let thread_1_flag = Arc::new(AtomicBool::new(false));

        let thread_2_key = 2;
        let thread_2_data = b"22222222";
        let thread_2_flag = Arc::new(AtomicBool::new(false));

        let iocp_1 = iocp.clone();
        let num_pending_1 = num_pending.clone();
        let thread_1_flag_clone = thread_1_flag.clone();
        let t_1 = thread::spawn(move || {
            do_the_thing(&iocp_1, file_name, thread_1_key, thread_1_data, &num_pending_1, &thread_1_flag_clone);
        });

        let iocp_2 = iocp.clone();
        let num_pending_2 = num_pending.clone();
        let thread_2_flag_clone = thread_2_flag.clone();
        let t_2 = thread::spawn(move || {
            do_the_thing(&iocp_2, file_name, thread_2_key, thread_2_data, &num_pending_2, &thread_2_flag_clone);
        });

        while num_pending.load(Ordering::SeqCst) > 0 {
            let result = iocp.wait_infinite();

            match result {
                IOCPResult::IOComplete(ioresult) => {
                    match ioresult.key {
                        // Thread 1 async IO completed.
                        1 => {
                            assert_eq!(ioresult.bytes_transferred, thread_1_data.len());
                            num_pending.fetch_sub(1, Ordering::SeqCst);
                            thread_1_flag.store(true, Ordering::SeqCst);
                        },
                        // Thread 2 async IO completed.
                        2 => {
                            assert_eq!(ioresult.bytes_transferred, thread_2_data.len());
                            num_pending.fetch_sub(1, Ordering::SeqCst);
                            thread_2_flag.store(true, Ordering::SeqCst);
                        }
                        _ => { unreachable!(); }
                    }
                }
                _ => { unreachable!(); }
            }
        }

        t_2.join().unwrap();
        t_1.join().unwrap();

        // Open the file for reading and make sure it's the correct length at least.
        // There's no easy way to guarantee file contents when writen to from multiple threads
        // as writes are generally speaking non-atomic (although they *can* be).
        let read_file = fs::File::open(file_name).unwrap();
        let metadata = read_file.metadata().unwrap();
        let len = metadata.len();

        assert_eq!(len, (thread_1_data.len() + thread_2_data.len()) as u64);

        fs::remove_file(file_name).unwrap();
    }
}