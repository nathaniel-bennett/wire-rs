// Copyright (c) 2022 Nathaniel Bennett
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![cfg_attr(not(feature = "std"), no_std)]

mod reader;
mod writer;

pub use reader::{
    VectoredCursor, VectoredRead, VectoredReadPart, VectoredReadRef, VectoredReader, WireCursor,
    WireRead, WireReadComp, WireReadPart, WireReadRef, WireReader,
};

pub use writer::{
    VectoredBufMut, VectoredCursorMut, VectoredWrite, VectoredWritePart, VectoredWriter,
    WireCursorMut, WireWrite, WireWritePart, WireWriter,
};

use core::convert;
use reader::*;
use writer::*;

#[derive(Clone, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum WireError {
    InsufficientBytes,
    ExtraBytes,
    InvalidData(&'static str),
    IntegerOverflow,
    Internal,
}

pub struct WireIndex {
    pub vectored_idx: usize,
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
