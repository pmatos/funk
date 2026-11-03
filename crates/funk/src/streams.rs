//! funk's standard input, output and error (ADR-2026-11-03-0107).
//!
//! The standard library's handles take `EBADF` for the end of the input on
//! standard input and for a successful write on standard output and error.
//! A descriptor open in the wrong mode, such as a standard output open only
//! for reading, gives `EBADF` on every read or write, so through them funk
//! would read an empty text or lose its output. On Unix, funk therefore
//! reads and writes each one through a `File` on a duplicate of its
//! descriptor, which reports `EBADF` like any other error. A descriptor
//! that was closed when funk started fails every read and write
//! (ADR-2026-11-02-2253): the standard library opened `/dev/null` on it.

use std::io::{self, Read, Write};

use funk_start_fds::{Stream, closed_at_start};

/// The bytes of standard input.
pub fn read_stdin() -> io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    open(Stream::Stdin, handle::stdin)?.read_to_end(&mut bytes)?;
    Ok(bytes)
}

/// Standard output, buffered by line as the standard library's is.
pub fn stdout() -> Output<impl Write> {
    Output(open(Stream::Stdout, handle::stdout))
}

/// Standard error, unbuffered as the standard library's is.
pub fn stderr() -> Output<impl Write> {
    Output(open(Stream::Stderr, handle::stderr))
}

/// A standard stream that funk writes, or the error that keeps funk from
/// using it, which every write then returns.
pub struct Output<W>(io::Result<W>);

impl<W: Write> Write for Output<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match &mut self.0 {
            Ok(w) => w.write(buf),
            Err(e) => Err(io::Error::new(e.kind(), e.to_string())),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match &mut self.0 {
            Ok(w) => w.flush(),
            Err(_) => Ok(()),
        }
    }
}

/// The handle of `stream`, unless the stream was closed when funk started.
fn open<H>(stream: Stream, handle: fn() -> io::Result<H>) -> io::Result<H> {
    match closed_at_start(stream) {
        Some(e) => Err(e),
        None => handle(),
    }
}

/// On Unix, a `File` on a duplicate of each standard descriptor.
#[cfg(unix)]
mod handle {
    use std::fs::File;
    use std::io::{self, LineWriter};
    use std::os::fd::{AsFd, BorrowedFd};

    pub fn stdin() -> io::Result<File> {
        duplicate(io::stdin().as_fd())
    }

    pub fn stdout() -> io::Result<LineWriter<File>> {
        duplicate(io::stdout().as_fd()).map(LineWriter::new)
    }

    pub fn stderr() -> io::Result<File> {
        duplicate(io::stderr().as_fd())
    }

    fn duplicate(fd: BorrowedFd<'_>) -> io::Result<File> {
        Ok(File::from(fd.try_clone_to_owned()?))
    }
}

/// Elsewhere, the standard library's handles, as before.
#[cfg(not(unix))]
mod handle {
    use std::io;

    pub fn stdin() -> io::Result<io::Stdin> {
        Ok(io::stdin())
    }

    pub fn stdout() -> io::Result<io::StdoutLock<'static>> {
        Ok(io::stdout().lock())
    }

    pub fn stderr() -> io::Result<io::StderrLock<'static>> {
        Ok(io::stderr().lock())
    }
}
