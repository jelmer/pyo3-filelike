#![deny(missing_docs)]
#![doc = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/README.md"))]
use pyo3::prelude::*;

use pyo3::exceptions::{PyValueError, PyAttributeError};
use std::io::{Read, Write, Seek};
#[cfg(any(unix, target_os = "wasi"))]
use std::os::fd::{AsFd, BorrowedFd, RawFd};

use std::borrow::Cow;

/// Rust wrapper for a Python file-like object that implements the `io` protocol.
#[derive(Debug)]
pub struct PyBinaryFile(pyo3::PyObject);

impl<'py> IntoPyObject<'py> for PyBinaryFile {
    type Target = PyAny;

    type Output = Bound<'py, PyAny>;

    type Error = PyErr;

    fn into_pyobject(self, py: Python<'py>) -> Result<Self::Output, Self::Error> {
        let obj = self.0.clone_ref(py);
        Ok(obj.into_bound(py))
    }
}

impl Clone for PyBinaryFile{
    fn clone(&self) -> Self {
        Python::with_gil(|py| {
            PyBinaryFile::from(self.0.clone_ref(py))
        })
    }
}

impl Read for PyBinaryFile {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        Python::with_gil(|py| {
            let bytes = self.0.call_method1(py, "read", (buf.len(), ))?;
            let bytes = bytes.extract::<&[u8]>(py)?;
            let len = std::cmp::min(buf.len(), bytes.len());
            buf[..len].copy_from_slice(&bytes[..len]);
            Ok(len)
        })
    }
}

impl Write for PyBinaryFile {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        Python::with_gil(|py| {
            let bytes = pyo3::types::PyBytes::new(py, buf);
            self.0.call_method1(py, "write", (bytes, ))?;
            Ok(buf.len())
        })
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Python::with_gil(|py| {
            self.0.call_method0(py, "flush")?;
            Ok(())
        })
    }
}

impl Seek for PyBinaryFile {
    fn seek(&mut self, pos: std::io::SeekFrom) -> std::io::Result<u64> {
        Python::with_gil(|py| {
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
        Python::with_gil(|py| {
            let fd = self.0.call_method0(py, "fileno")?;
            let fd = fd.extract::<RawFd>(py)?;
            Ok::<BorrowedFd<'_>, PyErr>(unsafe { BorrowedFd::borrow_raw(fd) })
        }).unwrap()
    }
}

impl PyBinaryFile {
    fn new(file: PyObject) -> PyResult<Self> {
        let o = PyBinaryFile(file);
        o.check_mode('b')?;
        Ok(o)
    }

    fn check_mode(&self, expected_mode: char) -> PyResult<()> {
        Python::with_gil(|py| {
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
                Err(e) => return Err(e),
            }
        })
    }
}

impl From<pyo3::PyObject> for PyBinaryFile {
    fn from(obj: pyo3::PyObject) -> Self {
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
    inner: PyObject,
    buffer: Vec<u8>
}

impl PyTextFile {
    /// Create a new `PyTextFile` from a Python file-like object and an encoding.
    pub fn new(file: PyObject) -> PyResult<Self> {
        Ok(PyTextFile{ inner: file, buffer: Vec::new() })
    }
}

impl Read for PyTextFile {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        Python::with_gil(|py| {
            if self.buffer.len() >= buf.len() {
                buf.copy_from_slice(&self.buffer[..buf.len()]);
                self.buffer.drain(..buf.len());
                return Ok(buf.len());
            }
            let text = self.inner.call_method1(py, "read", (buf.len() - self.buffer.len(), ))?;
            if let Ok(t) = text.extract::<Cow<str>>(py) {
                self.buffer.extend_from_slice(t.as_bytes());
            } else {
                self.buffer.extend_from_slice(text.extract::<&[u8]>(py)?);
            }

            let len = std::cmp::min(self.buffer.len(), buf.len());
            buf[..len].copy_from_slice(&self.buffer[..len]);
            self.buffer.drain(..len);
            Ok(len)
        })
    }
}

impl From<pyo3::PyObject> for PyTextFile {
    fn from(obj: pyo3::PyObject) -> Self {
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

impl Clone for PyTextFile{
    fn clone(&self) -> Self {
        Python::with_gil(|py| {
            PyTextFile::from(self.inner.clone_ref(py))
        })
    }
}




#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_read() {
        Python::with_gil(|py| -> PyResult<()> {
            let io = py.import("io")?;
            let file = io.call_method1("BytesIO", (&b"hello"[..], ))?;
            let mut file = PyBinaryFile::from(file);
            let mut buf = [0u8; 5];
            file.read_exact(&mut buf)?;
            assert_eq!(&buf, b"hello");
            Ok(())
        }).unwrap();
    }

    #[test]
    fn test_read_notexact() {
        Python::with_gil(|py| -> PyResult<()> {
            let io = py.import("io")?;
            let file = io.call_method1("BytesIO", (&b"hello"[..], ))?;
            let mut file = PyBinaryFile::from(file);
            let mut buf = [0u8; 10];
            let n = file.read(&mut buf)?;
            assert_eq!(n, 5);
            assert_eq!(&buf[..n], b"hello");
            Ok(())
        }).unwrap();
    }

    #[test]
    fn test_read_eof() {
        Python::with_gil(|py| -> PyResult<()> {
            let io = py.import("io")?;
            let file = io.call_method1("BytesIO", (&b"hello"[..], ))?;
            let mut file = PyBinaryFile::from(file);
            let mut buf = [0u8; 6];
            let err = file.read_exact(&mut buf).unwrap_err();
            assert_eq!(err.kind(), std::io::ErrorKind::UnexpectedEof);
            Ok(())
        }).unwrap();
    }

    #[test]
    fn test_read_to_end() {
        Python::with_gil(|py| -> PyResult<()> {
            let io = py.import("io")?;
            let file = io.call_method1("BytesIO", (&b"hello"[..], ))?;
            let mut file = PyBinaryFile::from(file);
            let mut buf = Vec::new();
            file.read_to_end(&mut buf)?;
            assert_eq!(&buf, b"hello");
            Ok(())
        }).unwrap();
    }

    #[test]
    fn test_write() {
        Python::with_gil(|py| {
            let io = py.import("io")?;
            let file = io.call_method1("BytesIO", (&b""[..], ))?;
            let mut file = PyBinaryFile::from(file);
            file.write_all(b"hello ")?;
            file.write_all(b"world")?;
            assert_eq!(file.0.call_method0(py, "getvalue")?.extract::<&[u8]>(py)?, b"hello world");
            Ok::<(), PyErr>(())
        }).unwrap();
    }

    #[test]
    fn test_seek() {
        Python::with_gil(|py| {
            let io = py.import("io")?;
            let file = io.call_method1("BytesIO", (&b"hello"[..], ))?;
            let mut file = PyBinaryFile::from(file);
            file.seek(std::io::SeekFrom::Start(1))?;
            let mut buf = [0u8; 4];
            file.read_exact(&mut buf)?;
            assert_eq!(&buf, b"ello");
            Ok::<(), PyErr>(())
        }).unwrap();
    }

    #[test]
    fn test_flush() {
        Python::with_gil(|py| {
            let io = py.import("io")?;
            let file = io.call_method1("BytesIO", (&b""[..], ))?;
            let mut file = PyBinaryFile::from(file);
            file.write_all(b"hello")?;
            file.flush()?;
            assert_eq!(file.0.call_method0(py, "getvalue")?.extract::<&[u8]>(py)?, b"hello");
            Ok::<(), PyErr>(())
        }).unwrap();
    }

    #[test]
    fn test_read_text() {
        Python::with_gil(|py| -> PyResult<()> {
            let io = py.import("io")?;
            let file = io.call_method1("StringIO", ("hello world", ))?;
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
        }).unwrap();
    }

    #[test]
    fn test_read_text_unicode() {
        // read halfway through a unicode character
        let io = Python::with_gil(|py| -> PyResult<PyObject> {
            let io = py.import("io")?;
            let file = io.call_method1("StringIO", ("hello \u{1f600} world", ))?;
            Ok(file.into())
        }).unwrap();

        let mut file = PyTextFile::from(io);
        let mut buf = [0u8; 7];
        file.read_exact(&mut buf).unwrap();
        assert_eq!(&buf, b"hello \xf0");

        let mut buf = [0u8; 1];
        file.read_exact(&mut buf).unwrap();
        assert_eq!(&buf, b"\x9f");
    }
}
