#![cfg_attr(not(feature = "std"), no_std)]

mod reader;

pub use reader::{
    CompWireReadable, PartVectoredReadable, PartWireReadable, RefVectoredReadable, RefWireReadable,
    VectoredCursor, VectoredReadable, VectoredReader, WireCursor, WireReadable, WireReader,
};

use core::convert;
use reader::*;

#[derive(Clone, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum WireError {
    InsufficientBytes,
    ExtraBytes,
    InvalidData(&'static str),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_read_finalize() {
        let bytes = [0x12, 0x34, 0x56, 0x78];
        let mut r1 = WireReader::<true>::new(&bytes);

        let val1 = r1.read();
        let val2 = r1.read();
        let val3 = WireReader::finalize_after(r1.read(), &r1);

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

    impl<'a> CompWireReadable<'a> for CustomWireReadable<'a> {
        fn from_wire_comp<const E: bool>(curs: &mut WireCursor<'a>) -> Result<Self, WireError> {
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
