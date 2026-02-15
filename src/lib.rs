#![deny(missing_docs)]
#![doc = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/README.md"))]
use pyo3::prelude::*;

use pyo3::exceptions::{PyAttributeError, PyValueError};
use std::io::{Read, Seek, Write};
#[cfg(any(unix, target_os = "wasi"))]
use std::os::fd::{AsFd, BorrowedFd, RawFd};

use std::borrow::Cow;

/// Rust wrapper for a Python file-like object that implements the `io` protocol.
#[derive(Debug)]
pub struct PyBinaryFile(Py<PyAny>);

impl<'py> IntoPyObject<'py> for PyBinaryFile {
    type Target = PyAny;

    type Output = Bound<'py, PyAny>;

    type Error = PyErr;

    fn into_pyobject(self, py: Python<'py>) -> Result<Self::Output, Self::Error> {
        let obj = self.0.clone_ref(py);
        Ok(obj.into_bound(py))
    }
}

impl Clone for PyBinaryFile {
    fn clone(&self) -> Self {
        Python::attach(|py| PyBinaryFile::from(self.0.clone_ref(py)))
    }
}

impl Read for PyBinaryFile {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        Python::attach(|py| {
            let bytes = self.0.call_method1(py, "read", (buf.len(),))?;
            let bytes = bytes
                .extract::<&[u8]>(py)
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e.to_string()))?;
            let len = std::cmp::min(buf.len(), bytes.len());
            buf[..len].copy_from_slice(&bytes[..len]);
            Ok(len)
        })
    }
}

impl Write for PyBinaryFile {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        Python::attach(|py| {
            let bytes = pyo3::types::PyBytes::new(py, buf);
            self.0.call_method1(py, "write", (bytes,))?;
            Ok(buf.len())
        })
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Python::attach(|py| {
            self.0.call_method0(py, "flush")?;
            Ok(())
        })
    }
}

impl Seek for PyBinaryFile {
    fn seek(&mut self, pos: std::io::SeekFrom) -> std::io::Result<u64> {
        Python::attach(|py| {
            let (whence, offset) = match pos {
                std::io::SeekFrom::Start(offset) => (0, offset as i64),
                std::io::SeekFrom::End(offset) => (2, offset),
                std::io::SeekFrom::Current(offset) => (1, offset),
            };
            let pos = self.0.call_method1(py, "seek", (offset, whence))?;
            let pos = pos.extract::<u64>(py)?;
            Ok(pos)
        })
    }
}

#[cfg(any(unix, target_os = "wasi"))]
impl AsFd for PyBinaryFile {
    fn as_fd(&self) -> BorrowedFd<'_> {
        Python::attach(|py| {
            let fd = self.0.call_method0(py, "fileno")?;
            let fd = fd.extract::<RawFd>(py)?;
            Ok::<BorrowedFd<'_>, PyErr>(unsafe { BorrowedFd::borrow_raw(fd) })
        })
        .unwrap()
    }
}

impl PyBinaryFile {
    fn new(file: Py<PyAny>) -> PyResult<Self> {
        let o = PyBinaryFile(file);
        o.check_mode('b')?;
        Ok(o)
    }

    fn check_mode(&self, expected_mode: char) -> PyResult<()> {
        Python::attach(|py| {
            match self.0.getattr(py, "mode") {
                Ok(mode) => {
                    let mode_str = match mode.extract::<Cow<str>>(py) {
                        Ok(mode_str) => mode_str,
                        Err(_) => {
                            // Assume binary mode if mode attribute is not a string
                            return Ok(());
                        }
                    };
                    if mode_str.contains(expected_mode) {
                        return Ok(());
                    }
                    Err(PyValueError::new_err(format!(
                        "file must be opened in {} mode",
                        expected_mode
                    )))
                }
                Err(e) if e.is_instance_of::<PyAttributeError>(py) => {
                    // Assume binary mode if mode attribute is not present
                    Ok(())
                }
                Err(e) => Err(e),
            }
        })
    }

    /// Check if the underlying Python file-like object supports seeking.
    ///
    /// This method calls the Python `seekable()` method on the underlying object
    /// to determine if seek operations are supported at runtime.
    ///
    /// Note: This must be checked at runtime rather than compile time because:
    /// - The wrapped Python object is dynamically typed (`Py<PyAny>`)
    /// - Whether seeking is supported depends on the specific Python object's
    ///   implementation, which cannot be known at compile time
    /// - Rust's trait system operates on static types, but Python objects have
    ///   runtime capabilities that vary between instances
    ///
    /// # Returns
    ///
    /// Returns `Ok(true)` if the file supports seeking, `Ok(false)` if not,
    /// or `Err` if the `seekable()` method call fails.
    ///
    /// # Example
    ///
    /// ```
    /// use pyo3::prelude::*;
    /// use pyo3_filelike::PyBinaryFile;
    ///
    /// Python::attach(|py| -> PyResult<()> {
    ///     let io = py.import("io")?;
    ///     let file = io.call_method1("BytesIO", (&b"hello"[..],))?;
    ///     let file = PyBinaryFile::from(file);
    ///     assert_eq!(file.seekable()?, true);
    ///     Ok(())
    /// }).unwrap();
    /// ```
    pub fn seekable(&self) -> PyResult<bool> {
        Python::attach(|py| {
            let result = self.0.call_method0(py, "seekable")?;
            result.extract::<bool>(py)
        })
    }
}

impl From<Py<PyAny>> for PyBinaryFile {
    fn from(obj: Py<PyAny>) -> Self {
        PyBinaryFile::new(obj).unwrap()
    }
}

impl From<Bound<'_, PyAny>> for PyBinaryFile {
    fn from(obj: Bound<'_, PyAny>) -> Self {
        PyBinaryFile::new(obj.into()).unwrap()
    }
}

/// Rust wrapper for a Python text file-like object that implements the `io` protocol.
///
/// This wrapper is similar to `PyBinaryFile`, but it assumes that the file is text and
/// returns the byte representation of the text.
///
/// The Python file-like object must have a `read` method that returns either a
/// `bytes` object or a `str` object.
///
/// Seek operations are not supported on text files, since the equivalent Python
/// file-like objects seek by characters, not bytes.
#[derive(Debug)]
pub struct PyTextFile {
    inner: Py<PyAny>,
    buffer: Vec<u8>,
}

impl PyTextFile {
    /// Create a new `PyTextFile` from a Python file-like object and an encoding.
    pub fn new(file: Py<PyAny>) -> PyResult<Self> {
        Ok(PyTextFile {
            inner: file,
            buffer: Vec::new(),
        })
    }

    /// Check if the underlying Python file-like object supports seeking.
    ///
    /// This method calls the Python `seekable()` method on the underlying object
    /// to determine if seek operations are supported at runtime.
    ///
    /// Note: This must be checked at runtime rather than compile time because:
    /// - The wrapped Python object is dynamically typed (`Py<PyAny>`)
    /// - Whether seeking is supported depends on the specific Python object's
    ///   implementation, which cannot be known at compile time
    /// - Rust's trait system operates on static types, but Python objects have
    ///   runtime capabilities that vary between instances
    ///
    /// # Returns
    ///
    /// Returns `Ok(true)` if the file supports seeking, `Ok(false)` if not,
    /// or `Err` if the `seekable()` method call fails.
    ///
    /// # Example
    ///
    /// ```
    /// use pyo3::prelude::*;
    /// use pyo3_filelike::PyTextFile;
    ///
    /// Python::attach(|py| -> PyResult<()> {
    ///     let io = py.import("io")?;
    ///     let file = io.call_method1("StringIO", ("hello",))?;
    ///     let file = PyTextFile::from(file);
    ///     assert_eq!(file.seekable()?, true);
    ///     Ok(())
    /// }).unwrap();
    /// ```
    pub fn seekable(&self) -> PyResult<bool> {
        Python::attach(|py| {
            let result = self.inner.call_method0(py, "seekable")?;
            result.extract::<bool>(py)
        })
    }
}

impl Read for PyTextFile {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        Python::attach(|py| {
            if self.buffer.len() >= buf.len() {
                buf.copy_from_slice(&self.buffer[..buf.len()]);
                self.buffer.drain(..buf.len());
                return Ok(buf.len());
            }
            let text = self
                .inner
                .call_method1(py, "read", (buf.len() - self.buffer.len(),))?;
            if let Ok(t) = text.extract::<Cow<str>>(py) {
                self.buffer.extend_from_slice(t.as_bytes());
            } else {
                self.buffer
                    .extend_from_slice(text.extract::<&[u8]>(py).map_err(|e| {
                        std::io::Error::new(std::io::ErrorKind::InvalidData, e.to_string())
                    })?);
            }

            let len = std::cmp::min(self.buffer.len(), buf.len());
            buf[..len].copy_from_slice(&self.buffer[..len]);
            self.buffer.drain(..len);
            Ok(len)
        })
    }
}

impl From<Py<PyAny>> for PyTextFile {
    fn from(obj: Py<PyAny>) -> Self {
        PyTextFile::new(obj).unwrap()
    }
}

impl From<Bound<'_, PyAny>> for PyTextFile {
    fn from(obj: Bound<'_, PyAny>) -> Self {
        PyTextFile::new(obj.into()).unwrap()
    }
}

impl<'py> IntoPyObject<'py> for PyTextFile {
    type Target = PyAny;

    type Output = Bound<'py, PyAny>;

    type Error = PyErr;

    fn into_pyobject(self, py: Python<'py>) -> Result<Self::Output, Self::Error> {
        let obj = self.inner.clone_ref(py);
        Ok(obj.into_bound(py))
    }
}

impl Clone for PyTextFile {
    fn clone(&self) -> Self {
        Python::attach(|py| PyTextFile::from(self.inner.clone_ref(py)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyo3::ffi::c_str;

    #[test]
    fn test_read() {
        Python::attach(|py| -> PyResult<()> {
            let io = py.import("io")?;
            let file = io.call_method1("BytesIO", (&b"hello"[..],))?;
            let mut file = PyBinaryFile::from(file);
            let mut buf = [0u8; 5];
            file.read_exact(&mut buf)?;
            assert_eq!(&buf, b"hello");
            Ok(())
        })
        .unwrap();
    }

    #[test]
    fn test_read_notexact() {
        Python::attach(|py| -> PyResult<()> {
            let io = py.import("io")?;
            let file = io.call_method1("BytesIO", (&b"hello"[..],))?;
            let mut file = PyBinaryFile::from(file);
            let mut buf = [0u8; 10];
            let n = file.read(&mut buf)?;
            assert_eq!(n, 5);
            assert_eq!(&buf[..n], b"hello");
            Ok(())
        })
        .unwrap();
    }

    #[test]
    fn test_read_eof() {
        Python::attach(|py| -> PyResult<()> {
            let io = py.import("io")?;
            let file = io.call_method1("BytesIO", (&b"hello"[..],))?;
            let mut file = PyBinaryFile::from(file);
            let mut buf = [0u8; 6];
            let err = file.read_exact(&mut buf).unwrap_err();
            assert_eq!(err.kind(), std::io::ErrorKind::UnexpectedEof);
            Ok(())
        })
        .unwrap();
    }

    #[test]
    fn test_read_to_end() {
        Python::attach(|py| -> PyResult<()> {
            let io = py.import("io")?;
            let file = io.call_method1("BytesIO", (&b"hello"[..],))?;
            let mut file = PyBinaryFile::from(file);
            let mut buf = Vec::new();
            file.read_to_end(&mut buf)?;
            assert_eq!(&buf, b"hello");
            Ok(())
        })
        .unwrap();
    }

    #[test]
    fn test_write() {
        Python::attach(|py| {
            let io = py.import("io")?;
            let file = io.call_method1("BytesIO", (&b""[..],))?;
            let mut file = PyBinaryFile::from(file);
            file.write_all(b"hello ")?;
            file.write_all(b"world")?;
            assert_eq!(
                file.0.call_method0(py, "getvalue")?.extract::<&[u8]>(py)?,
                b"hello world"
            );
            Ok::<(), PyErr>(())
        })
        .unwrap();
    }

    #[test]
    fn test_seek() {
        Python::attach(|py| {
            let io = py.import("io")?;
            let file = io.call_method1("BytesIO", (&b"hello"[..],))?;
            let mut file = PyBinaryFile::from(file);
            file.seek(std::io::SeekFrom::Start(1))?;
            let mut buf = [0u8; 4];
            file.read_exact(&mut buf)?;
            assert_eq!(&buf, b"ello");
            Ok::<(), PyErr>(())
        })
        .unwrap();
    }

    #[test]
    fn test_flush() {
        Python::attach(|py| {
            let io = py.import("io")?;
            let file = io.call_method1("BytesIO", (&b""[..],))?;
            let mut file = PyBinaryFile::from(file);
            file.write_all(b"hello")?;
            file.flush()?;
            assert_eq!(
                file.0.call_method0(py, "getvalue")?.extract::<&[u8]>(py)?,
                b"hello"
            );
            Ok::<(), PyErr>(())
        })
        .unwrap();
    }

    #[test]
    fn test_read_text() {
        Python::attach(|py| -> PyResult<()> {
            let io = py.import("io")?;
            let file = io.call_method1("StringIO", ("hello world",))?;
            let mut file = PyTextFile::from(file);
            let mut buf = [0u8; 5];
            file.read_exact(&mut buf)?;
            assert_eq!(&buf, b"hello");
            file.read_exact(&mut buf)?;
            assert_eq!(&buf, b" worl");
            let mut buf = Vec::new();
            file.read_to_end(&mut buf).unwrap();
            assert_eq!(&buf, b"d");
            Ok(())
        })
        .unwrap();
    }

    #[test]
    fn test_read_text_unicode() {
        // read halfway through a unicode character
        let io = Python::attach(|py| -> PyResult<Py<PyAny>> {
            let io = py.import("io")?;
            let file = io.call_method1("StringIO", ("hello \u{1f600} world",))?;
            Ok(file.into())
        })
        .unwrap();

        let mut file = PyTextFile::from(io);
        let mut buf = [0u8; 7];
        file.read_exact(&mut buf).unwrap();
        assert_eq!(&buf, b"hello \xf0");

        let mut buf = [0u8; 1];
        file.read_exact(&mut buf).unwrap();
        assert_eq!(&buf, b"\x9f");
    }

    #[test]
    fn test_seekable_binary() {
        Python::attach(|py| -> PyResult<()> {
            let io = py.import("io")?;
            let file = io.call_method1("BytesIO", (&b"hello"[..],))?;
            let file = PyBinaryFile::from(file);
            assert_eq!(file.seekable()?, true);
            Ok(())
        })
        .unwrap();
    }

    #[test]
    fn test_seekable_text() {
        Python::attach(|py| -> PyResult<()> {
            let io = py.import("io")?;
            let file = io.call_method1("StringIO", ("hello",))?;
            let file = PyTextFile::from(file);
            assert_eq!(file.seekable()?, true);
            Ok(())
        })
        .unwrap();
    }

    #[test]
    fn test_non_seekable_binary() {
        Python::attach(|py| -> PyResult<()> {
            // Create a custom non-seekable file-like object
            let locals = pyo3::types::PyDict::new(py);
            py.run(
                c_str!(
                    r#"class NonSeekableFile:
    def __init__(self):
        self.data = b"hello"
        self.pos = 0

    def read(self, n=-1):
        if n == -1:
            result = self.data[self.pos:]
            self.pos = len(self.data)
        else:
            result = self.data[self.pos:self.pos + n]
            self.pos += len(result)
        return result

    def write(self, data):
        return len(data)

    def flush(self):
        pass

    def seekable(self):
        return False

    @property
    def mode(self):
        return 'rb'

file = NonSeekableFile()"#
                ),
                None,
                Some(&locals),
            )?;
            let file = locals.get_item("file")?.unwrap();
            let file = PyBinaryFile::from(file);
            assert_eq!(file.seekable()?, false);
            Ok(())
        })
        .unwrap();
    }

    #[test]
    fn test_non_seekable_text() {
        Python::attach(|py| -> PyResult<()> {
            // Create a custom non-seekable file-like object
            let locals = pyo3::types::PyDict::new(py);
            py.run(
                c_str!(
                    r#"class NonSeekableTextFile:
    def __init__(self):
        self.data = "hello"
        self.pos = 0

    def read(self, n=-1):
        if n == -1:
            result = self.data[self.pos:]
            self.pos = len(self.data)
        else:
            result = self.data[self.pos:self.pos + n]
            self.pos += len(result)
        return result

    def seekable(self):
        return False

file = NonSeekableTextFile()"#
                ),
                None,
                Some(&locals),
            )?;
            let file = locals.get_item("file")?.unwrap();
            let file = PyTextFile::from(file);
            assert_eq!(file.seekable()?, false);
            Ok(())
        })
        .unwrap();
    }
}
