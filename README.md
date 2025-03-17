# Rust compatible wrappers for file-like objects in Python

This crate provides implementations of the ``Write``, ``Seek``, ``Read`` and ``AsRawFd``
rust traits on top of file-like objects in PyO3.

## Example

```rust
let o = pyo3::Python::with_gil(|py| {
    let io = py.import("io")?;
    io.call_method1("BytesIO", ("hello",))
})?;
let f = py3o_filelike::PyBinaryFile::from(o);

let mut buf = [0u8; 4];
f.read_exact(&mut buf)?;
assert_eq!(&buf, b"hell");
```
