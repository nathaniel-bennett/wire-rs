use crate::WireError;
use core::{mem, str};
#[cfg(feature = "std")]
use std::io;

const UTF8_DECODE_ERROR: &str = "failed to decode UTF8--invalid character sequence";

#[cfg(feature = "std")]
type VectoredBuf<'a> = &'a [io::IoSlice<'a>];
#[cfg(not(feature = "std"))]
type VectoredBuf<'a> = &'a [&'a [u8]];

pub trait WireReadable: Sized {
    fn from_wire<const E: bool>(curs: &mut WireCursor<'_>) -> Result<Self, WireError>;

    // Add once try_from_fn is stabilized
    /*
    fn array_from_wire<const L: usize, const E: bool>(curs: &mut WireCursor<'_>) -> Result<[Self; L], WireError> {
        std::array::try_from_fn(|_| { Self::from_wire::<E>(curs) })
    }
    */
}

// Can contain both owned types and references. Useful for structs that have both byte buffers (&'a [u8]) and values (u16, i32, etc)
pub trait CompWireReadable<'a>: Sized {
    fn from_wire_comp<const E: bool>(curs: &mut WireCursor<'a>) -> Result<Self, WireError>;

    // Add once try_from_fn is stabilized
    /*
    fn array_from_wire<const L: usize, const E: bool>(curs: &mut WireCursor<'_>) -> Result<[Self; L], WireError> {
        std::array::try_from_fn(|_| { Self::from_wire::<E>(curs) })
    }
    */
}

pub trait PartWireReadable: Sized {
    fn from_wire_part<const L: usize, const E: bool>(
        curs: &mut WireCursor<'_>,
    ) -> Result<Self, WireError>;
}

pub trait RefWireReadable {
    fn from_wire_ref<'a>(curs: &mut WireCursor<'a>, size: usize) -> Result<&'a Self, WireError>;
}

pub trait VectoredReadable: Sized {
    fn from_vectored<const E: bool>(curs: &mut VectoredCursor<'_>) -> Result<Self, WireError>;

    /*
    fn array_from_vectored<const L: usize, const E: bool>(curs: &mut VectoredCursor<'_>) -> Result<[Self; L], WireError> {
        std::array::try_from_fn(|_| { Self::from_vectored::<E>(curs) })
    }
    */
}

pub trait PartVectoredReadable: Sized {
    fn from_vectored_part<const L: usize, const E: bool>(
        curs: &mut VectoredCursor<'_>,
    ) -> Result<Self, WireError>;
}

pub trait RefVectoredReadable {
    fn from_vectored_ref<'a, const E: bool>(
        curs: &mut VectoredCursor<'_>,
        size: usize,
    ) -> Result<&'a Self, WireError>;
}

#[derive(Clone, Copy)]
pub struct WireCursor<'a> {
    wire: &'a [u8],
}

impl<'a> WireCursor<'a> {
    fn new(wire: &'a [u8]) -> Self {
        WireCursor { wire }
    }

    pub fn get_readable<T, const E: bool>(&mut self) -> Result<T, WireError>
    where
        T: WireReadable,
    {
        T::from_wire::<E>(self)
    }

    pub fn get_readable_part<T, const L: usize, const E: bool>(&mut self) -> Result<T, WireError>
    where
        T: PartWireReadable,
    {
        T::from_wire_part::<L, E>(self)
    }

    pub fn get_readable_ref<T, const E: bool>(&mut self, length: usize) -> Result<&'a T, WireError>
    where
        T: RefWireReadable + ?Sized,
    {
        T::from_wire_ref(self, length)
    }

    pub fn get_readable_comp<T, const E: bool>(&mut self) -> Result<T, WireError>
    where
        T: CompWireReadable<'a> + ?Sized,
    {
        T::from_wire_comp::<E>(self)
    }

    pub fn advance(&mut self, amount: usize) -> Result<(), WireError> {
        self.wire = match self.wire.get(amount..) {
            Some(w) => w,
            None => return Err(WireError::InsufficientBytes),
        };
        Ok(())
    }

    pub fn advance_up_to(&mut self, amount: usize) {
        self.wire = match self.wire.get(amount..) {
            Some(w) => w,
            None => &[],
        };
    }

    pub fn get(&mut self, amount: usize) -> Result<&'a [u8], WireError> {
        // self.wire.try_split_at() would be cleaner, but doesn't exist as an API yet...
        match (self.wire.get(0..amount), self.wire.get(amount..)) {
            (Some(r), Some(w)) => {
                self.wire = w;
                Ok(r)
            }
            _ => Err(WireError::InsufficientBytes),
        }
    }

    pub fn get_array<const L: usize>(&mut self) -> Result<&'a [u8; L], WireError> {
        //self.wire.try_split_array_ref() would be cleaner, but doesn't exist as an API yet...
        match (self.wire.get(0..L), self.wire.get(L..)) {
            (Some(r), Some(w)) => {
                self.wire = w;
                r.try_into().map_err(|_| WireError::Internal)
            }
            _ => Err(WireError::InsufficientBytes),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.wire.is_empty()
    }

    pub fn remaining(&self) -> usize {
        self.wire.len()
    }
}

#[derive(Clone, Copy)]
pub struct VectoredCursor<'a> {
    wire: VectoredBuf<'a>,
    idx: usize,
}

impl<'a> VectoredCursor<'a> {
    fn new(wire: VectoredBuf<'a>) -> Self {
        VectoredCursor { wire, idx: 0 }
    }

    pub fn is_empty(&self) -> bool {
        let mut tmp_wire = self.wire;
        let mut tmp_idx = self.idx;
        while let Some((first, next_slices)) = tmp_wire.split_first() {
            if tmp_idx < first.len() {
                return false;
            } else {
                tmp_idx = 0;
                tmp_wire = next_slices;
            }
        }

        true
    }

    pub fn get_next(&mut self) -> Result<u8, WireError> {
        while let Some((first, next_slices)) = self.wire.split_first() {
            match first.get(self.idx) {
                Some(val) => {
                    self.idx += 1;
                    return Ok(*val);
                }
                None => {
                    self.idx = 0;
                    self.wire = next_slices;
                }
            }
        }

        Err(WireError::InsufficientBytes)
    }

    pub fn try_get(&mut self, amount: usize) -> Option<&[u8]> {
        while let Some((first, next_slices)) = self.wire.split_first() {
            if self.idx >= first.len() {
                self.idx = 0;
                self.wire = next_slices;
                continue;
            }

            let end_idx = match self.idx.checked_add(amount) {
                Some(i) => i,
                None => return None, // Can't have a slice of length greater than `usize::MAX`
            };

            match first.get(self.idx..end_idx) {
                Some(slice) => {
                    self.idx += amount;
                    return Some(slice);
                }
                None => return None,
            }
        }

        None
    }

    pub fn try_get_array<const L: usize>(&mut self) -> Option<&[u8; L]> {
        match self.try_get(L) {
            Some(arr) => arr.try_into().ok(), // Invariant: should always be Ok
            None => None,
        }
    }

    pub fn remaining(&self) -> usize {
        self.wire
            .iter()
            .map(|s| s.len())
            .sum::<usize>()
            .saturating_sub(self.idx)
    }

    pub fn skip(&mut self, mut amount: usize) -> Result<(), WireError> {
        while let Some((first, next_slices)) = self.wire.split_first() {
            let remaining_slice_len = match first.len().checked_sub(self.idx) {
                None | Some(0) => {
                    // Invariant: None should never occur, as the index should never exceed the bound of the first slice
                    self.wire = next_slices;
                    self.idx = 0;
                    continue;
                }
                Some(l) => l,
            };

            match amount.checked_sub(remaining_slice_len) {
                Some(0) => {
                    self.wire = next_slices;
                    self.idx = 0;
                    return Ok(());
                }
                Some(new_amount) => {
                    self.wire = next_slices;
                    self.idx = 0;
                    amount = new_amount;
                }
                None => {
                    self.idx += amount; // Invariant: cannot overflow (as you cannot have a slice greater than `usize::MAX`)
                    return Ok(());
                }
            }
        }

        Err(WireError::InsufficientBytes)
    }
}

pub struct WireReader<'a, const E: bool = true> {
    curs: WireCursor<'a>,
    initial_len: usize,
}

impl<'a, const E: bool> WireReader<'a, E> {
    pub fn new(bytes: &'a [u8]) -> Self {
        WireReader {
            curs: WireCursor::new(bytes),
            initial_len: bytes.len(),
        }
    }

    pub fn new_with_endianness<const F: bool>(bytes: &'a [u8]) -> WireReader<'a, F> {
        WireReader::<F> {
            curs: WireCursor::new(bytes),
            initial_len: bytes.len(),
        }
    }

    pub fn advance(&mut self, amount: usize) -> Result<(), WireError> {
        let mut temp_curs = self.curs;
        let res = temp_curs.advance(amount);
        if res.is_ok() {
            self.curs = temp_curs;
        }
        res
    }

    pub fn advance_up_to(&mut self, amount: usize) {
        self.curs.advance_up_to(amount);
    }

    pub fn finalize(&self) -> Result<(), WireError> {
        if !self.is_empty() {
            Err(WireError::ExtraBytes)
        } else {
            Ok(())
        }
    }

    pub fn finalize_after<T>(action: Result<T, WireError>, reader: &Self) -> Result<T, WireError> {
        if action.is_ok() {
            reader.finalize()?;
        }
        action
    }

    pub fn is_empty(&self) -> bool {
        self.curs.is_empty()
    }

    pub fn peek<T>(&self) -> Result<T, WireError>
    where
        T: WireReadable,
    {
        let mut temp_curs = self.curs;
        T::from_wire::<E>(&mut temp_curs)
    }

    pub fn peek_sized<T>(&self, size: usize) -> Result<&'a T, WireError>
    where
        T: RefWireReadable + ?Sized,
    {
        let mut temp_curs = self.curs;
        T::from_wire_ref(&mut temp_curs, size)
    }

    pub fn read<T>(&mut self) -> Result<T, WireError>
    where
        T: WireReadable,
    {
        let mut temp_curs = self.curs;
        let res = T::from_wire::<E>(&mut temp_curs);
        if res.is_ok() {
            self.curs = temp_curs;
        }
        res
    }

    // add once array_from_wire is added
    /*
    pub fn read_array<T, const L: usize>(&mut self) -> Result<[T; L], WireError>
    where T: WireReadable {
        T::array_from_wire::<L, E>(self.curs)
    }
    */

    pub fn read_part<T, const L: usize>(&mut self) -> Result<T, WireError>
    where
        T: PartWireReadable,
    {
        let mut temp_curs = self.curs;
        let res = T::from_wire_part::<L, E>(&mut temp_curs);
        if res.is_ok() {
            self.curs = temp_curs;
        }
        res
    }

    pub fn read_ref<T>(&mut self, size: usize) -> Result<&'a T, WireError>
    where
        T: RefWireReadable + ?Sized,
    {
        let mut temp_curs = self.curs;
        let res = T::from_wire_ref(&mut temp_curs, size);
        if res.is_ok() {
            self.curs = temp_curs;
        }
        res
    }

    pub fn read_comp<T>(&mut self) -> Result<T, WireError>
    where
        T: CompWireReadable<'a>,
    {
        let mut temp_curs = self.curs;
        let res = T::from_wire_comp::<E>(&mut temp_curs);
        if res.is_ok() {
            self.curs = temp_curs;
        }
        res
    }

    pub fn read_remaining<T>(&mut self) -> Result<&'a T, WireError>
    where
        T: RefWireReadable + ?Sized,
    {
        self.read_ref(self.curs.remaining())
    }
}

pub fn _internal_wirereader_consumed(reader: &WireReader<'_>) -> usize {
    reader.initial_len - reader.curs.remaining()
}

pub struct VectoredReader<'a, const E: bool = true> {
    curs: VectoredCursor<'a>,
    initial_slice_cnt: usize,
}

impl<'a, const E: bool> VectoredReader<'a, E> {
    pub fn new(bytes: VectoredBuf<'a>) -> Self {
        VectoredReader {
            curs: VectoredCursor::new(bytes),
            initial_slice_cnt: bytes.len(),
        }
    }

    pub fn new_with_endianness<const F: bool>(bytes: VectoredBuf<'a>) -> VectoredReader<'a, F> {
        VectoredReader::<F> {
            curs: VectoredCursor::new(bytes),
            initial_slice_cnt: bytes.len(),
        }
    }

    pub fn advance(&mut self, amount: usize) -> Result<(), WireError> {
        self.curs.skip(amount)
    }

    pub fn advance_up_to(&mut self, index: usize) {
        match self.advance(index) {
            Ok(_) => (),
            Err(_) => self.curs = VectoredCursor::new(&[]), // advance() isn't guaranteed to advance cursor to end on failure (though it does right now)
        }
    }

    pub fn finalize(&self) -> Result<(), WireError> {
        if !self.is_empty() {
            Err(WireError::ExtraBytes)
        } else {
            Ok(())
        }
    }

    pub fn finalize_after<T>(action: Result<T, WireError>, reader: &Self) -> Result<T, WireError> {
        if action.is_ok() {
            reader.finalize()?;
        }
        action
    }

    pub fn is_empty(&self) -> bool {
        self.curs.is_empty()
    }

    pub fn peek<T>(&self) -> Result<T, WireError>
    where
        T: VectoredReadable,
    {
        let mut temp_curs = self.curs; // Cheap and easy to just copy cursor and discard
        T::from_vectored::<E>(&mut temp_curs)
    }

    pub fn peek_sized<T>(&self, size: usize) -> Result<&'a T, WireError>
    where
        T: RefVectoredReadable,
    {
        let mut temp_curs = self.curs;
        T::from_vectored_ref::<E>(&mut temp_curs, size)
    }

    pub fn read<T>(&mut self) -> Result<T, WireError>
    where
        T: VectoredReadable,
    {
        T::from_vectored::<E>(&mut self.curs)
    }

    pub fn read_partial<T, const L: usize>(&mut self) -> Result<T, WireError>
    where
        T: PartVectoredReadable,
    {
        T::from_vectored_part::<L, E>(&mut self.curs)
    }

    pub fn read_remaining<T>(&mut self) -> Result<&'a T, WireError>
    where
        T: RefVectoredReadable,
    {
        self.read_sized(self.curs.remaining())
    }

    pub fn read_sized<T>(&mut self, size: usize) -> Result<&'a T, WireError>
    where
        T: RefVectoredReadable,
    {
        T::from_vectored_ref::<E>(&mut self.curs, size)
    }

    /*
    pub fn read_array<T, const L: usize>(&mut self) -> Result<[T; L], WireError>
    where T: WireReadable {
        let (ret, consumed) = T::array_from_wire(self.wire)?;
        self.advance_up_to(consumed);
        Ok(ret)
    }
    */
}

pub fn _internal_vectoredreader_vec_index(reader: &VectoredReader<'_>) -> usize {
    reader.initial_slice_cnt - reader.curs.wire.len()
}

pub fn _internal_vectoredreader_slice_index(reader: &VectoredReader<'_>) -> usize {
    reader.curs.idx
}

// Implementations of RefWireReadable for base types

impl RefWireReadable for [u8] {
    fn from_wire_ref<'a>(curs: &mut WireCursor<'a>, size: usize) -> Result<&'a Self, WireError> {
        curs.get(size)
    }
}

impl RefWireReadable for str {
    fn from_wire_ref<'a>(curs: &mut WireCursor<'a>, size: usize) -> Result<&'a Self, WireError> {
        curs.get(size).and_then(|bytes| {
            str::from_utf8(bytes).map_err(|_| WireError::InvalidData(UTF8_DECODE_ERROR))
        })
    }
}

macro_rules! derive_wire_readable {
    ($int:ty)=> {
        impl WireReadable for $int {
            fn from_wire<const E: bool>(curs: &mut WireCursor<'_>) -> Result<Self, WireError> {
                if E {
                    Ok(<$int>::from_be_bytes(*curs.get_array::<{ mem::size_of::<$int>() }>()?))
                } else {
                    Ok(<$int>::from_le_bytes(*curs.get_array::<{ mem::size_of::<$int>() }>()?))
                }
            }
        }
    };

    ($i1:ty, $($i2:ty),+) => {
        derive_wire_readable! { $i1 }
        derive_wire_readable! { $($i2),+ }
    };
}

macro_rules! derive_wire_partreadable {
    ($int:ty)=> {
        impl PartWireReadable for $int {
            fn from_wire_part<const L: usize, const E: bool>(curs: &mut WireCursor<'_>) -> Result<Self, WireError> {
                assert!(L < mem::size_of::<$int>()); // TODO: once more powerful const generic expressions are in rust, use them
                let mut res = [0; mem::size_of::<$int>()];
                let bytes = curs.get_array::<L>()?;

                if E {
                    for (i, b) in bytes.iter().rev().enumerate() {
                        res[i] = *b; // Fill first L bytes in reverse order (be -> le)
                    }
                } else {
                    for (i, b) in bytes.iter().enumerate() {
                        res[i] = *b;
                    }
                }

                Ok(<$int>::from_le_bytes(res)) // Most computers are natively little-endian, so this will be a slightly faster transmutate
            }
        }
    };

    ($i1:ty, $($i2:ty),+) => {
        derive_wire_partreadable! { $i1 }
        derive_wire_partreadable! { $($i2),+ }
    };
}

macro_rules! derive_vectored_readable {
    ($int:ty)=> {
        impl VectoredReadable for $int {
            fn from_vectored<const E: bool>(curs: &mut VectoredCursor<'_>) -> Result<Self, WireError> {
                // Try the more efficient try_get_array; fall back to getting byte by byte on failure
                let arr = match curs.try_get_array::<{ mem::size_of::<$int>() }>() {
                    Some(a) => *a,
                    None => {
                        let mut tmp_arr = [0; mem::size_of::<$int>()];
                        for b in tmp_arr.iter_mut() {
                            *b = curs.get_next()?;
                        }

                        tmp_arr
                    },
                };

                if E {
                    Ok(<$int>::from_be_bytes(arr))
                } else {
                    Ok(<$int>::from_le_bytes(arr))
                }
            }
        }
    };

    ($i1:ty, $($i2:ty),+) => {
        derive_vectored_readable! { $i1 }
        derive_vectored_readable! { $($i2),+ }
    };
}

macro_rules! derive_vectored_partreadable {
    ($int:ty)=> {
        impl PartVectoredReadable for $int {
            fn from_vectored_part<const L: usize, const E: bool>(curs: &mut VectoredCursor<'_>) -> Result<Self, WireError> {
                assert!(L < mem::size_of::<$int>()); // TODO: once more powerful const generic expressions are in rust, use them
                let mut res = [0; mem::size_of::<$int>()];

                // Try the more efficient try_get_array; fall back to getting byte by byte on failure
                let bytes = match curs.try_get_array::<L>() {
                    Some(a) => *a,
                    None => {
                        let mut tmp_arr = [0; L];
                        for b in tmp_arr.iter_mut() {
                            *b = curs.get_next()?;
                        }

                        tmp_arr
                    },
                };

                if E {
                    for (i, b) in bytes.iter().rev().enumerate() {
                        res[i] = *b; // Fill first L bytes in reverse order (be -> le)
                    }
                } else {
                    for (i, b) in bytes.iter().enumerate() {
                        res[i] = *b;
                    }
                }

                Ok(<$int>::from_le_bytes(res)) // Most computers are natively little-endian, so this will be a slightly faster transmutate
            }
        }
    };

    ($i1:ty, $($i2:ty),+) => {
        derive_vectored_partreadable! { $i1 }
        derive_vectored_partreadable! { $($i2),+ }
    };
}

derive_wire_readable!(i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, f32, f64, isize, usize);
derive_vectored_readable!(i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, f32, f64, isize, usize);

// No floats or signed integers--their implementations aren't conducive to chopping off bytes at will
derive_wire_partreadable!(u16, u32, u64, u128, usize);
derive_vectored_partreadable!(u16, u32, u64, u128, usize);
