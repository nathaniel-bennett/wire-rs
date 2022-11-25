// Copyright (c) 2022 Nathaniel Bennett
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Extensible interface for converting data to/from wire protocols.
//!
//! The purpose of this crate is to provide a simplified interface for reading from/writing to a
//! buffer of bytes in an efficient and memory-safe way. It provides default implementations for
//! reading/writing primitive types--integers (u8, i32, f64, etc), strings (&str), byte slices
//! and arrays (&[u8; 3]). It also offers extensibilty to other types and more complex structs
//! via traits ([`WireRead`], [`WireWrite`], and their variants).
//!
//! In addition to supporting standard single-slice buffers, this crate provides equivalent
//! support for non-contiguous buffers by means of the [`VectoredReader`] and [`VectoredWriter`],
//! along with corresponding [`VectoredRead`] and [`VectoredWrite`] traits and their variants.
//! Instead of operating on a single slice (`&[u8]`), these operate on a slice of slices
//! (`&[&[u8]]`) and transparently handle reading from/writing to a chunk that spans multiple
//! slices. This can be useful in cases where it is not desirable or feasible to guarantee
//! contiguous memory--ring buffers, two-dimensional arrays, `iovec` API calls,
//! `PACKET_MMAP` buffers and the like.
//!
//! The Reader and Writer data structures exposed by this crate are effectively light-weight
//! wrappers around slices, meaning that they can be created, copied and dropped freely with
//! very little memory overhead.

// TODO: add example use here

#![cfg_attr(not(feature = "std"), no_std)]

mod reader;
mod writer;

pub use reader::{
    VectoredCursor, VectoredRead, VectoredReadComp, VectoredReadPart, VectoredReadRef,
    VectoredReader, WireCursor, WireRead, WireReadComp, WireReadPart, WireReadRef, WireReader,
};

pub use writer::{
    VectoredBufMut, VectoredCursorMut, VectoredWrite, VectoredWritePart, VectoredWriter,
    WireCursorMut, WireWrite, WireWritePart, WireWriter,
};

use core::convert;
use reader::*;
use writer::*;

/// An error in reading from or writing to a wire.
///
/// New error types may be added to this enum, so it should not be exhaustively matched against.
#[non_exhaustive]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum WireError {
    /// Returned when a Reader or Writer contains too few remaining bytes to fully read or write
    /// the desired type.
    InsufficientBytes,
    /// Returned when some bytes remain on the wire after the final data type is read or written.
    ///
    /// The `finalize()` or `finalize_after()` methods can be used to check that all of the slice
    /// passed into a Reader or Writer is used. This is particularly useful for wire protocols
    /// that include a length field at the beginning of a packet that needs to be validated.
    /// When bytes remain in a Reader or Writer and one of the above methods is called, the
    /// `InsufficientBytes` error will be returned.
    ExtraBytes,
    /// Returned when the type being read requires a particular format that the bytes on the
    /// wire do not adhere to, or when the type being written is not within a certain range of
    /// values that can be serialized.
    ///
    /// The latter case can only occur for types that implement either the [`WireWritePart`]
    /// trait or the [`VectoredWritePart`] trait. For example, the following would return an
    /// `InvalidData` error:
    ///
    /// ```rust
    /// use wire_rs::{WireError, WireWriter};
    ///
    /// fn decode_partial_out_of_range() -> Result<(), WireError> {
    ///     let mut buf = [0u8; 4];
    ///     let out_of_range = 0x0100u16;
    ///     let mut writer: WireWriter = WireWriter::new(buf.as_mut_slice());
    ///     writer.write_part::<u16, 1>(&out_of_range) // Returns Err(WireError::InvalidData)
    /// }
    /// ```
    ///
    /// Whereas a number within the range of values that can be encoded for the given size
    /// would return Ok(()):
    ///
    /// ```rust
    /// use wire_rs::{WireError, WireWriter};
    ///
    /// fn decode_partial_within_range() -> Result<(), WireError> {
    ///     let mut buf = [0u8; 4];
    ///     let within_range = 0xFFu64;
    ///     let mut writer: WireWriter = WireWriter::new(buf.as_mut_slice());
    ///     writer.write_part::<u64, 1>(&within_range)
    ///     // Returns Ok(())
    /// }
    /// ```
    ///
    /// As an example of the former case, a Reader would return an error when invalid UTF-8
    /// is read in for a `str` type, such as:
    ///
    /// ```rust
    /// use wire_rs::{WireError, WireReader};
    ///
    /// fn decode_bad_utf8() -> Result<(), WireError> {
    ///     let buf = [0xC3, 0x28]; // Invalid 2-octet UTF-8 sequence
    ///     let mut reader: WireReader = WireReader::new(buf.as_slice());
    ///     let s: &str = reader.read_remaining()?;
    ///     // Returns Err(WireError::InvalidData)
    ///     return Ok(())
    /// }
    /// ```
    InvalidData(&'static str),
    /// An internal error in the Reader or Writer.
    ///
    /// This will not be raised unless there is some bug in the implementation of the Reader of
    /// Writer, most likely caused by an invariant not holding. If encountered, this error should
    /// be counted as a fatal error in (de/)serializing data from the wire, and the Reader or
    /// Writer that returned this error should not be used for subsequent operations.
    Internal,
}

/// An index of a buffer or vectored buffers.
///
/// This type is created from a Wire or Vectored Reader/Writer type.
/// Its primary use is to provide a mechanism for advancing a slice or vectored slice
/// up by the amount consumed by the Reader/Writer without causing any lifetime issues.
///
/// Readers and Writers carry a reference to the buffer they are reading,
/// which means that no mutations can be performed on the referenced buffer while a Reader is
/// in scope. Converting a reader into a `WireIndex` provides a mechanism to drop the Reader
/// while retaining the index that the Reader had reached. Once the buffer has been mutated
/// (e.g. additional data being written into it), a slice of the new contents (starting at the
/// index stored in the `WireIndex`) can be used to create a new Reader. That reader can then
/// continue to extract data from the buffer.
pub struct WireIndex {
    /// The index of which buffer in the set of vectored buffers the reader or writer was at.
    ///
    /// If the given `WireIndex` was created from a [`WireReader`] or [`WireWriter`] and not a
    /// [`VectoredReader`] or [`VectoredWriter`], this value will always be set to 0.
    pub vectored_idx: usize,
    /// The index within the buffer that the reader or writer was at.
    pub slice_idx: usize,
}

impl convert::From<WireReader<'_>> for WireIndex {
    fn from(reader: WireReader<'_>) -> Self {
        WireIndex {
            vectored_idx: 0,
            slice_idx: _internal_wirereader_consumed(&reader),
        }
    }
}

impl convert::From<VectoredReader<'_>> for WireIndex {
    fn from(reader: VectoredReader<'_>) -> Self {
        WireIndex {
            vectored_idx: _internal_vectoredreader_vec_index(&reader),
            slice_idx: _internal_vectoredreader_slice_index(&reader),
        }
    }
}

impl convert::From<WireWriter<'_>> for WireIndex {
    fn from(writer: WireWriter<'_>) -> Self {
        WireIndex {
            vectored_idx: 0,
            slice_idx: _internal_wirewriter_consumed(&writer),
        }
    }
}

impl convert::From<VectoredWriter<'_>> for WireIndex {
    fn from(writer: VectoredWriter<'_>) -> Self {
        WireIndex {
            vectored_idx: _internal_vectoredwriter_vec_index(&writer),
            slice_idx: _internal_vectoredwriter_slice_index(&writer),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const BUF1_LEN: usize = 16;
    const BUF1: [u8; BUF1_LEN] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
        0x0f,
    ];

    #[test]
    fn vectored_final_index() {
        let iovec1: [&[u8]; 3] = [&BUF1[BUF1_LEN..], &BUF1[..11], &[]];

        let mut r1 = VectoredReader::new(&iovec1);
        assert!(r1.read() == Ok(0x0001020304050607u64));
        assert!(r1.read() == Ok(0x0809i16));
        assert!(r1.read() == Ok(0x0au8));
        let i1 = WireIndex::from(r1);
        assert!(i1.vectored_idx == 1);
        assert!(i1.slice_idx == 11);

        let mut r1 = VectoredReader::new(&iovec1);
        assert!(r1.read_remaining() == Ok(&BUF1[..11]));
        let i1 = WireIndex::from(r1);
        assert!(i1.vectored_idx == 1);
        assert!(i1.slice_idx == 11);
    }

    #[test]
    fn vectored_empty_index() {
        let iovec1: [&[u8]; 6] = [&[], &[], &BUF1[..4], &[], &BUF1[4..8], &[]];
        let mut r1 = VectoredReader::new(&iovec1);
        let i1 = WireIndex::from(r1);
        assert!(i1.vectored_idx == 0);
        assert!(i1.slice_idx == 0);
        assert!(r1.read::<i128>().is_err());
        let i2 = WireIndex::from(r1);
        assert!(i2.vectored_idx == 0);
        assert!(i2.slice_idx == 0);
        assert!(r1.read::<i32>() == Ok(0x00010203i32));
        let i3 = WireIndex::from(r1);
        assert!(i3.vectored_idx == 2);
        assert!(i3.slice_idx == 4);

        assert!(r1.read::<i32>() == Ok(0x04050607i32));
        assert!(r1.finalize().is_ok());
        let i4 = WireIndex::from(r1);

        assert!(i4.vectored_idx == 4);
        assert!(i4.slice_idx == 4);
    }

    #[test]
    fn vectored_wraparound_empty() {
        let iovec1: [&[u8]; 2] = [&BUF1[BUF1_LEN..], &BUF1[..11]];

        let mut r1 = VectoredReader::new(&iovec1);
        assert!(r1.read::<u128>().is_err());
        let i1 = WireIndex::from(r1);
        assert!(i1.vectored_idx == 0);
        assert!(i1.slice_idx == 0);

        let mut r1 = VectoredReader::new(&iovec1);
        assert!(r1.read::<u8>().is_ok());
        let i1 = WireIndex::from(r1);
        assert!(i1.vectored_idx == 1);
        assert!(i1.slice_idx == 1);

        let iovec2: [&[u8]; 2] = [&BUF1[BUF1_LEN - 4..], &BUF1[..7]];

        let mut r2 = VectoredReader::new(&iovec2);
        assert!(r2.read::<u128>().is_err());
        let i2 = WireIndex::from(r2);
        assert!(i2.vectored_idx == 0);
        assert!(i2.slice_idx == 0);

        let mut r2 = VectoredReader::new(&iovec2);
        assert!(r2.read::<u32>().is_ok());
        let i2 = WireIndex::from(r2);
        assert!(i2.vectored_idx == 0);
        assert!(i2.slice_idx == 4);

        let mut r2 = VectoredReader::new(&iovec2);
        assert!(r2.read::<u8>().is_ok());
        assert!(r2.read::<u32>().is_ok());
        let i2 = WireIndex::from(r2);
        assert!(i2.vectored_idx == 1);
        assert!(i2.slice_idx == 1);
    }

    #[test]
    fn simple_read_finalize() {
        let bytes = [0x12, 0x34, 0x56, 0x78];
        let mut r1: WireReader = WireReader::new(&bytes);

        let val1 = r1.read();
        let val2 = r1.read();
        let val3 = WireReader::finalize_after(r1.read(), &r1);
        //        let i1 = WireIndex::from(r1);

        assert!(val1 == Ok(0x12u8));
        assert!(val2 == Ok(0x34u8));
        assert!(val3 == Ok(0x5678u16));
    }

    #[test]
    fn read_finalize_insufficient_bytes() {
        let bytes = [0x12, 0x34, 0x56, 0x78];
        let mut r1 = WireReader::<true>::new(&bytes);

        let val1 = r1.read();
        let val2 = r1.read();
        let val3: Result<u32, WireError> = WireReader::finalize_after(r1.read(), &r1);

        assert!(val1 == Ok(0x12u8));
        assert!(val2 == Ok(0x34u8));
        assert!(val3 == Err(WireError::InsufficientBytes));
    }

    #[test]
    fn read_str() {
        let bytes = [0x12, 0x34, 0x56, 0x78];
        let mut r1 = WireReader::<true>::new(&bytes);
        let str1 = r1.read_ref(4);

        assert!(str1 == Ok("\x12\x34\x56\x78"));
        assert!(r1.finalize() == Ok(()));
    }

    #[test]
    fn read_nonutf8_str_fail() {
        let bytes = [0x9a, 0xbc, 0xde, 0xf0];
        let mut r1 = WireReader::<true>::new(&bytes);
        let str1 = r1.read_ref::<str>(4);

        assert!(str1.is_err());
        assert!(match str1 {
            Err(WireError::InvalidData(_)) => true,
            _ => false,
        });
    }

    struct CustomWireReadable<'a> {
        a: u8,
        b: &'a str,
    }

    impl<'a> WireReadComp<'a> for CustomWireReadable<'a> {
        fn read_wire_comp<const E: bool>(curs: &mut WireCursor<'a>) -> Result<Self, WireError> {
            // curs needs some stronger functionality

            let a = curs.get_readable::<u8, E>()?;
            let str_len = curs.get_readable::<u16, E>()?;

            Ok(CustomWireReadable {
                a: a,
                b: curs.get_readable_ref::<str, E>(str_len as usize)?,
            })
        }
    }

    #[test]
    fn custom_wire_readable() {
        let bytes = [0x9a, 0x00, 0x05, 0x65, 0x66, 0x67, 0x68, 0x69];
        let c1: CustomWireReadable;

        // c1's lifetime must be bound to `bytes`, not `r1`, so this should be able to compile
        {
            let mut r1 = WireReader::<true>::new(&bytes);
            c1 = r1.read_comp().unwrap_or(CustomWireReadable { a: 0, b: "" });

            assert!(r1.is_empty())
        }

        assert!(c1.a == 0x9a);
        assert!(c1.b == "\x65\x66\x67\x68\x69")
    }
}
