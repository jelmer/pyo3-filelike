/// This crate provides a wrapper for file-like objects in Python that implement the `io`
/// protocol, and allows them to be used as `Read`, `Write`, and `Seek` traits in Rust.
///
/// Objects need to implement the `io` protocol. For the `Read` trait, the object must have a
/// `read` method that takes a single argument, the number of bytes to read, and returns a `bytes`
/// object. For the `Write` trait, the object must have a `write` method that takes a single
/// argument, a `bytes` object. For the `Seek` trait, the object must have a `seek` method that
/// takes two arguments, the offset and whence, and returns the new position.
///
/// The `mode` attribute is checked to ensure that the file is opened in binary mode.
/// If the `mode` attribute is not present, the file is assumed to be opened in binary mode.
///
/// The `AsFd` trait is implemented for Unix-like systems, allowing the file to be used with
/// functions that take a file descriptor. The `fileno` method is called to get the file
/// descriptor.
///
/// # Example
///
/// ```rust
/// use pyo3::prelude::*;
/// use std::io::{Read, Write};
///
/// pyo3::Python::with_gil(|py| -> PyResult<()> {
///    let io = py.import("io")?;
///    let file = io.call_method1("BytesIO", (&b"hello"[..], ))?;
///    let mut file = pyo3_filelike::PyBinaryFile::from(file);
///    let mut buf = [0u8; 5];
///    file.read_exact(&mut buf)?;
///    assert_eq!(&buf, b"hello");
///    Ok(())
/// }).unwrap();

use pyo3::prelude::*;
use pyo3::exceptions::{PyValueError, PyAttributeError};
use std::io::{Read, Write, Seek};
#[cfg(any(unix, target_os = "wasi"))]
use std::os::fd::{AsFd, BorrowedFd, RawFd};

/// Rust wrapper for a Python file-like object that implements the `io` protocol.
#[derive(Debug)]
pub struct PyBinaryFile(pyo3::PyObject);

impl ToPyObject for PyBinaryFile {
    fn to_object(&self, py: Python) -> PyObject {
        self.0.clone_ref(py)
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
            let bytes = pyo3::types::PyBytes::new_bound(py, buf);
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
                    if mode.extract::<&str>(py)?.contains(expected_mode) {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_read() {
        Python::with_gil(|py| -> PyResult<()> {
            let io = py.import_bound("io")?;
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
            let io = py.import_bound("io")?;
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
            let io = py.import_bound("io")?;
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
            let io = py.import_bound("io")?;
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
            let io = py.import_bound("io")?;
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
            let io = py.import_bound("io")?;
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
            let io = py.import_bound("io")?;
            let file = io.call_method1("BytesIO", (&b""[..], ))?;
            let mut file = PyBinaryFile::from(file);
            file.write_all(b"hello")?;
            file.flush()?;
            assert_eq!(file.0.call_method0(py, "getvalue")?.extract::<&[u8]>(py)?, b"hello");
            Ok::<(), PyErr>(())
        }).unwrap();
    }

}
