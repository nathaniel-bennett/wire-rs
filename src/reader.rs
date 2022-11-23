// Copyright (c) 2022 Nathaniel Bennett
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use crate::WireError;
use core::{mem, str};

#[cfg(feature = "ioslice")]
use std::io;

const UTF8_DECODE_ERROR: &str = "failed to decode UTF8--invalid character sequence";
const NONCONTIGUOUS_SEGMENT: &str =
    "could not get contiguous slice--data split in 2 or more segments";

#[cfg(feature = "ioslice")]
type VectoredBuf<'a> = &'a [io::IoSlice<'a>];
#[cfg(not(feature = "ioslice"))]
pub type VectoredBuf<'a> = &'a [&'a [u8]];

/// Serialization to an owned data type from the wire.
pub trait WireRead: Sized {
    fn read_wire<const E: bool>(curs: &mut WireCursor<'_>) -> Result<Self, WireError>;

    // Add once try_from_fn is stabilized
    /*
    fn array_from_wire<const L: usize, const E: bool>(curs: &mut WireCursor<'_>) -> Result<[Self; L], WireError> {
        std::array::try_from_fn(|_| { Self::from_wire::<E>(curs) })
    }
    */
}

// Can contain both owned types and references. Useful for structs that have both byte buffers (&'a [u8]) and values (u16, i32, etc)
pub trait WireReadComp<'a>: Sized {
    fn read_wire_comp<const E: bool>(curs: &mut WireCursor<'a>) -> Result<Self, WireError>;

    // Add once try_from_fn is stabilized
    /*
    fn array_from_wire<const L: usize, const E: bool>(curs: &mut WireCursor<'_>) -> Result<[Self; L], WireError> {
        std::array::try_from_fn(|_| { Self::from_wire::<E>(curs) })
    }
    */
}

pub trait WireReadPart: Sized {
    fn read_wire_part<const L: usize, const E: bool>(
        curs: &mut WireCursor<'_>,
    ) -> Result<Self, WireError>;
}

pub trait WireReadRef {
    fn read_wire_ref<'a>(curs: &mut WireCursor<'a>, size: usize) -> Result<&'a Self, WireError>;
}

pub trait VectoredRead: Sized {
    fn read_vectored<const E: bool>(curs: &mut VectoredCursor<'_>) -> Result<Self, WireError>;

    /*
    fn array_from_vectored<const L: usize, const E: bool>(curs: &mut VectoredCursor<'_>) -> Result<[Self; L], WireError> {
        std::array::try_from_fn(|_| { Self::from_vectored::<E>(curs) })
    }
    */
}

pub trait VectoredReadPart: Sized {
    fn read_vectored_part<const L: usize, const E: bool>(
        curs: &mut VectoredCursor<'_>,
    ) -> Result<Self, WireError>;
}

pub trait VectoredReadRef {
    fn read_vectored_ref<'a>(
        curs: &mut VectoredCursor<'a>,
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
        T: WireRead,
    {
        T::read_wire::<E>(self)
    }

    pub fn get_readable_part<T, const L: usize, const E: bool>(&mut self) -> Result<T, WireError>
    where
        T: WireReadPart,
    {
        T::read_wire_part::<L, E>(self)
    }

    pub fn get_readable_ref<T, const E: bool>(&mut self, length: usize) -> Result<&'a T, WireError>
    where
        T: WireReadRef + ?Sized,
    {
        T::read_wire_ref(self, length)
    }

    // Composite
    pub fn get_readable_comp<T, const E: bool>(&mut self) -> Result<T, WireError>
    where
        T: WireReadComp<'a> + ?Sized,
    {
        T::read_wire_comp::<E>(self)
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

    pub fn get_slice(&mut self, amount: usize) -> Result<&'a [u8], WireError> {
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

    pub fn advance(&mut self, mut amount: usize) -> Result<(), WireError> {
        while let Some((first, next_slices)) = self.wire.split_first() {
            let remaining_slice_len = match first.len().checked_sub(self.idx) {
                None | Some(0) if next_slices.is_empty() => {
                    return Err(WireError::InsufficientBytes)
                }
                None | Some(0) => {
                    // Invariant: None should never occur, as the index should never exceed the bound of the first slice
                    self.wire = next_slices;
                    self.idx = 0;
                    continue;
                }
                Some(l) => l,
            };

            match amount.checked_sub(remaining_slice_len) {
                None | Some(0) => {
                    self.idx += amount; // Invariant: cannot overflow (as you cannot have a slice greater than `usize::MAX`)
                    return Ok(());
                }
                Some(new_amount) => {
                    self.wire = next_slices;
                    self.idx = 0;
                    amount = new_amount;
                }
            }
        }

        Err(WireError::InsufficientBytes)
    }

    pub fn advance_up_to(&mut self, mut amount: usize) {
        while let Some((first, next_slices)) = self.wire.split_first() {
            let remaining_slice_len = match first.len().checked_sub(self.idx) {
                None | Some(0) if next_slices.is_empty() => return,
                None | Some(0) => {
                    // Invariant: None should never occur, as the index should never exceed the bound of the first slice
                    self.wire = next_slices;
                    self.idx = 0;
                    continue;
                }
                Some(l) => l,
            };

            match amount.checked_sub(remaining_slice_len) {
                Some(0) | None => {
                    self.idx += amount; // Invariant: cannot overflow (as you cannot have a slice greater than `usize::MAX`)
                    return;
                }
                Some(_) if next_slices.is_empty() => {
                    self.idx = first.len();
                    return;
                }
                Some(new_amount) => {
                    self.wire = next_slices;
                    self.idx = 0;
                    amount = new_amount;
                }
            }
        }
    }

    pub fn is_empty(&self) -> bool {
        let mut tmp_wire = self.wire;
        let mut tmp_idx = self.idx;
        while let Some((first, next_slices)) = tmp_wire.split_first() {
            if tmp_idx < first.len() {
                return false;
            } else if next_slices.is_empty() {
                // tmp_idx is already first.len()
                return true;
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
                None if next_slices.is_empty() => return Err(WireError::InsufficientBytes),
                None => {
                    self.idx = 0;
                    self.wire = next_slices;
                }
            }
        }

        Err(WireError::InsufficientBytes)
    }

    pub fn try_get(&mut self, amount: usize) -> Option<&'a [u8]> {
        while let Some((first, next_slices)) = self.wire.split_first() {
            if self.idx >= first.len() && !next_slices.is_empty() {
                self.idx = 0;
                self.wire = next_slices;
                continue;
            }

            let end_idx = match self.idx.checked_add(amount) {
                Some(i) => i,
                None => return None, // Can't have a slice of length greater than `usize::MAX`
            };

            return match first.get(self.idx..end_idx) {
                Some(slice) => {
                    self.idx += amount;
                    Some(slice)
                }
                None => None,
            };
        }

        None
    }

    pub fn try_get_array<const L: usize>(&mut self) -> Option<&'a [u8; L]> {
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
}

#[derive(Clone, Copy)]
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
        T: WireRead,
    {
        let mut temp_curs = self.curs;
        T::read_wire::<E>(&mut temp_curs)
    }

    pub fn peek_sized<T>(&self, size: usize) -> Result<&'a T, WireError>
    where
        T: WireReadRef + ?Sized,
    {
        let mut temp_curs = self.curs;
        T::read_wire_ref(&mut temp_curs, size)
    }

    pub fn read<T>(&mut self) -> Result<T, WireError>
    where
        T: WireRead,
    {
        let mut temp_curs = self.curs;
        let res = T::read_wire::<E>(&mut temp_curs);
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
        T: WireReadPart,
    {
        let mut temp_curs = self.curs;
        let res = T::read_wire_part::<L, E>(&mut temp_curs);
        if res.is_ok() {
            self.curs = temp_curs;
        }
        res
    }

    pub fn read_ref<T>(&mut self, size: usize) -> Result<&'a T, WireError>
    where
        T: WireReadRef + ?Sized,
    {
        let mut temp_curs = self.curs;
        let res = T::read_wire_ref(&mut temp_curs, size);
        if res.is_ok() {
            self.curs = temp_curs;
        }
        res
    }

    pub fn read_comp<T>(&mut self) -> Result<T, WireError>
    where
        T: WireReadComp<'a>,
    {
        let mut temp_curs = self.curs;
        let res = T::read_wire_comp::<E>(&mut temp_curs);
        if res.is_ok() {
            self.curs = temp_curs;
        }
        res
    }

    pub fn read_remaining<T>(&mut self) -> Result<&'a T, WireError>
    where
        T: WireReadRef + ?Sized,
    {
        self.read_ref(self.curs.remaining())
    }
}

pub fn _internal_wirereader_consumed(reader: &WireReader<'_>) -> usize {
    reader.initial_len - reader.curs.remaining()
}

#[derive(Clone, Copy)]
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

    /*
    pub fn new_be(bytes: VectoredBuf<'a>) -> VectoredReader<'a, true> {
        VectoredReader::<true> {
            curs: VectoredCursor::new(bytes),
            initial_slice_cnt: bytes.len(),
        }
    }

    pub fn new_le(bytes: VectoredBuf<'a>) -> VectoredReader<'a, false> {
        VectoredReader::<false> {
            curs: VectoredCursor::new(bytes),
            initial_slice_cnt: bytes.len(),
        }
    }
    */

    pub fn advance(&mut self, amount: usize) -> Result<(), WireError> {
        let mut temp_curs = self.curs;
        let res = temp_curs.advance(amount);
        if res.is_ok() {
            self.curs = temp_curs;
        }
        res
    }

    pub fn advance_up_to(&mut self, index: usize) {
        self.curs.advance_up_to(index);
    }

    pub fn finalize(&self) -> Result<(), WireError> {
        if self.is_empty() {
            Ok(())
        } else {
            Err(WireError::ExtraBytes)
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
        T: VectoredRead,
    {
        let mut temp_curs = self.curs; // Cheap and easy to just copy cursor and discard
        T::read_vectored::<E>(&mut temp_curs)
    }

    pub fn peek_sized<T>(&self, size: usize) -> Result<&'a T, WireError>
    where
        T: VectoredReadRef + ?Sized,
    {
        let mut temp_curs = self.curs;
        T::read_vectored_ref(&mut temp_curs, size)
    }

    pub fn read<T>(&mut self) -> Result<T, WireError>
    where
        T: VectoredRead,
    {
        let mut temp_curs = self.curs;
        let res = T::read_vectored::<E>(&mut temp_curs);
        if res.is_ok() {
            self.curs = temp_curs;
        }
        res
    }

    pub fn read_partial<T, const L: usize>(&mut self) -> Result<T, WireError>
    where
        T: VectoredReadPart,
    {
        let mut temp_curs = self.curs;
        let res = T::read_vectored_part::<L, E>(&mut temp_curs);
        if res.is_ok() {
            self.curs = temp_curs;
        }
        res
    }

    pub fn read_remaining<T>(&mut self) -> Result<&'a T, WireError>
    where
        T: VectoredReadRef + ?Sized,
    {
        self.read_sized(self.curs.remaining())
    }

    pub fn read_sized<T>(&mut self, size: usize) -> Result<&'a T, WireError>
    where
        T: VectoredReadRef + ?Sized,
    {
        let mut temp_curs = self.curs;
        let res = T::read_vectored_ref(&mut temp_curs, size);
        if res.is_ok() {
            self.curs = temp_curs;
        }
        res
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

impl WireReadRef for [u8] {
    fn read_wire_ref<'a>(curs: &mut WireCursor<'a>, size: usize) -> Result<&'a Self, WireError> {
        curs.get_slice(size)
    }
}

impl WireReadRef for str {
    fn read_wire_ref<'a>(curs: &mut WireCursor<'a>, size: usize) -> Result<&'a Self, WireError> {
        curs.get_slice(size).and_then(|bytes| {
            str::from_utf8(bytes).map_err(|_| WireError::InvalidData(UTF8_DECODE_ERROR))
        })
    }
}

impl VectoredReadRef for [u8] {
    fn read_vectored_ref<'a>(
        curs: &mut VectoredCursor<'a>,
        size: usize,
    ) -> Result<&'a Self, WireError> {
        curs.try_get(size)
            .ok_or(WireError::InvalidData(NONCONTIGUOUS_SEGMENT))
    }
}

macro_rules! derive_wire_readable {
    ($int:ty)=> {
        impl WireRead for $int {
            fn read_wire<const E: bool>(curs: &mut WireCursor<'_>) -> Result<Self, WireError> {
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
        impl WireReadPart for $int {
            fn read_wire_part<const L: usize, const E: bool>(curs: &mut WireCursor<'_>) -> Result<Self, WireError> {
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
        impl VectoredRead for $int {
            fn read_vectored<const E: bool>(curs: &mut VectoredCursor<'_>) -> Result<Self, WireError> {
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
        impl VectoredReadPart for $int {
            fn read_vectored_part<const L: usize, const E: bool>(curs: &mut VectoredCursor<'_>) -> Result<Self, WireError> {
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
