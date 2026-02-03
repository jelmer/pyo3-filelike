# Rust compatible wrappers for file-like objects in Python

This crate provides a wrapper for file-like objects in Python that implement the `io`
protocol, and allows them to be used as `Read`, `Write`, and `Seek` traits in Rust.

Objects need to implement the `io` protocol. For the `Read` trait, the object must have a
`read` method that takes a single argument, the number of bytes to read, and returns a `bytes`
object. For the `Write` trait, the object must have a `write` method that takes a single
argument, a `bytes` object. For the `Seek` trait, the object must have a `seek` method that
takes two arguments, the offset and whence, and returns the new position.

The `mode` attribute is checked to ensure that the file is opened in binary mode.
If the `mode` attribute is not present, the file is assumed to be opened in binary mode.

The `AsFd` trait is implemented for Unix-like systems, allowing the file to be used with
functions that take a file descriptor. The `fileno` method is called to get the file
descriptor.

# Example

```rust
use pyo3::prelude::*;
use std::io::{Read, Write};

pyo3::Python::attach(|py| -> PyResult<()> {
   let io = py.import("io")?;
   let file = io.call_method1("BytesIO", (&b"hello"[..], ))?;
   let mut file = pyo3_filelike::PyBinaryFile::from(file);
   let mut buf = [0u8; 5];
   file.read_exact(&mut buf)?;
   assert_eq!(&buf, b"hello");
   Ok(())
}).unwrap();
