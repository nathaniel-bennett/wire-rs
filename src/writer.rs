// Copyright (c) 2022 Nathaniel Bennett
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use crate::WireError;
use core::{cmp, mem, str};

#[cfg(feature = "ioslice")]
use std::io;

#[cfg(feature = "ioslice")]
type VectoredBufMut<'a> = &'a [io::IoSliceMut<'a>];
#[cfg(not(feature = "ioslice"))]
pub type VectoredBufMut<'a> = &'a mut [&'a mut [u8]];

/// Serialization to an owned data type from the wire.
pub trait WireWrite {
    fn write_wire<const E: bool>(&self, curs: &mut WireCursorMut<'_>) -> Result<(), WireError>;
}

pub trait WireWritePart: Sized {
    fn write_wire_part<const L: usize, const E: bool>(
        &self,
        curs: &mut WireCursorMut<'_>,
    ) -> Result<(), WireError>;
}

pub trait VectoredWrite {
    fn write_vectored<const E: bool>(
        &self,
        curs: &mut VectoredCursorMut<'_>,
    ) -> Result<(), WireError>;
}

pub trait VectoredWritePart: Sized {
    fn write_vectored_part<const L: usize, const E: bool>(
        &self,
        curs: &mut VectoredCursorMut<'_>,
    ) -> Result<(), WireError>;
}

pub struct WireCursorMut<'a> {
    wire: &'a mut [u8],
    idx: usize,
}

impl<'a> WireCursorMut<'a> {
    fn new(wire: &'a mut [u8]) -> Self {
        WireCursorMut { wire, idx: 0 }
    }

    pub fn put_writable<T, const E: bool>(&mut self, writable: &T) -> Result<(), WireError>
    where
        T: WireWrite,
    {
        writable.write_wire::<E>(self)
    }

    pub fn put_writable_part<T, const L: usize, const E: bool>(
        &mut self,
        writable: &T,
    ) -> Result<(), WireError>
    where
        T: WireWritePart,
    {
        writable.write_wire_part::<L, E>(self)
    }

    pub fn advance(&mut self, amount: usize) -> Result<(), WireError> {
        self.idx = match self.idx.checked_add(amount) {
            Some(new_idx) if new_idx > self.wire.len() => return Err(WireError::InsufficientBytes),
            Some(new_idx) => new_idx,
            None => return Err(WireError::IntegerOverflow),
        };

        Ok(())
    }

    pub fn advance_up_to(&mut self, amount: usize) {
        self.idx = match self.idx.checked_add(amount) {
            Some(new_idx) => cmp::min(new_idx, self.wire.len()),
            None => self.wire.len(),
        };
    }

    pub fn is_empty(&self) -> bool {
        self.wire.is_empty()
    }

    pub fn put_slice(&mut self, slice: &[u8]) -> Result<(), WireError> {
        let tmp_slice = match self.wire.get_mut(self.idx..) {
            Some(s) => s,
            None => return Err(WireError::Internal),
        };

        if tmp_slice.len() < slice.len() {
            return Err(WireError::InsufficientBytes);
        }

        for (a, b) in tmp_slice.iter_mut().zip(slice.iter()) {
            *a = *b;
        }

        self.idx += slice.len();
        Ok(())
    }

    pub fn remaining(&self) -> usize {
        self.wire.len().saturating_sub(self.idx)
    }
}

pub struct VectoredCursorMut<'a> {
    wire: VectoredBufMut<'a>,
    arr_idx: usize,
    idx: usize,
}

impl<'a> VectoredCursorMut<'a> {
    fn new(wire: VectoredBufMut<'a>) -> Self {
        VectoredCursorMut {
            wire,
            arr_idx: 0,
            idx: 0,
        }
    }

    pub fn advance(&mut self, mut amount: usize) -> Result<(), WireError> {
        while let Some(curr_slice) = self.wire.get(self.arr_idx) {
            let remaining_slice_len = match curr_slice.len().checked_sub(self.idx) {
                None => return Err(WireError::Internal), // Invariant: None should never occur, as the index should never exceed the bound of the first slice
                Some(0) => {
                    if self.wire.get(self.arr_idx + 1).is_none() {
                        return Err(WireError::InsufficientBytes);
                    }

                    self.arr_idx += 1;
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
                    self.arr_idx += 1;
                    self.idx = 0;
                    amount = new_amount;
                }
            }
        }

        Err(WireError::InsufficientBytes)
    }

    pub fn advance_up_to(&mut self, mut amount: usize) {
        while let Some(curr_slice) = self.wire.get(self.arr_idx) {
            let remaining_slice_len = match curr_slice.len().checked_sub(self.idx) {
                None | Some(0) => {
                    // Invariant: None should never occur, as the index should never exceed the bound of the first slice
                    if self.wire.get(self.arr_idx + 1).is_none() {
                        return;
                    }
                    self.arr_idx += 1;
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
                Some(new_amount) => {
                    if self.wire.get(self.arr_idx + 1).is_none() {
                        self.idx = curr_slice.len();
                        return;
                    }
                    self.arr_idx += 1;
                    self.idx = 0;
                    amount = new_amount;
                }
            }
        }
    }

    pub fn put_writable<T, const E: bool>(&mut self, writable: &T) -> Result<(), WireError>
    where
        T: VectoredWrite,
    {
        writable.write_vectored::<E>(self)
    }

    pub fn put_writable_part<T, const L: usize, const E: bool>(
        &mut self,
        writable: &T,
    ) -> Result<(), WireError>
    where
        T: VectoredWritePart,
    {
        writable.write_vectored_part::<L, E>(self)
    }

    pub fn is_empty(&self) -> bool {
        let mut tmp_arr_idx = self.arr_idx;
        let mut tmp_idx = self.idx;
        while let Some(tmp_slice) = self.wire.get(tmp_arr_idx) {
            if tmp_idx < tmp_slice.len() {
                return false;
            } else if self.wire.get(tmp_arr_idx).is_none() {
                // tmp_idx == first.len() and we're at the last slice
                return true;
            } else {
                tmp_idx = 0;
                tmp_arr_idx += 1;
            }
        }

        true
    }

    // TODO: give this implementation some clean up
    pub fn put_slice(&mut self, mut slice: &[u8]) -> Result<(), WireError> {
        while let Some(tmp_slice) = self.wire.get_mut(self.arr_idx) {
            let remaining = match tmp_slice.get_mut(self.idx..) {
                Some(s) => s,
                None => return Err(WireError::Internal),
            };

            for (a, b) in remaining.iter_mut().zip(slice.iter()) {
                *a = *b;
            }

            let num_read = cmp::min(remaining.len(), slice.len());
            match slice.get(num_read..) {
                Some(&[]) => {
                    self.idx += num_read;
                    return Ok(());
                }
                Some(s) => {
                    if self.wire.get(self.arr_idx + 1).is_none() {
                        return Err(WireError::InsufficientBytes);
                    }
                    slice = s;
                    self.arr_idx += 1;
                    self.idx = 0;
                }
                None => return Err(WireError::Internal),
            }
        }

        Err(WireError::InsufficientBytes)
    }

    pub fn remaining(&self) -> usize {
        self.wire
            .iter()
            .map(|s| s.len())
            .sum::<usize>()
            .saturating_sub(self.idx)
    }
}

pub struct WireWriter<'a, const E: bool = true> {
    curs: WireCursorMut<'a>,
    initial_len: usize,
}

impl<'a, const E: bool> WireWriter<'a, E> {
    pub fn new(bytes: &'a mut [u8]) -> Self {
        let initial_len = bytes.len();
        WireWriter {
            curs: WireCursorMut::new(bytes),
            initial_len,
        }
    }

    pub fn advance(&mut self, amount: usize) -> Result<(), WireError> {
        let prev_idx = self.curs.idx;
        let res = self.curs.advance(amount);
        if res.is_err() {
            self.curs.idx = prev_idx;
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

    pub fn finalize_after<T>(
        action: Result<(), WireError>,
        reader: &Self,
    ) -> Result<(), WireError> {
        if action.is_ok() {
            reader.finalize()?;
        }
        action
    }

    pub fn is_empty(&self) -> bool {
        self.curs.is_empty()
    }

    pub fn write<T>(&mut self, writable: &T) -> Result<(), WireError>
    where
        T: WireWrite,
    {
        let temp_idx = self.curs.idx;
        let res = writable.write_wire::<E>(&mut self.curs);
        if res.is_err() {
            self.curs.idx = temp_idx;
        }
        res
    }

    pub fn write_part<T, const L: usize>(&mut self, writable: &T) -> Result<(), WireError>
    where
        T: WireWritePart,
    {
        let temp_idx = self.curs.idx;
        let res = writable.write_wire_part::<L, E>(&mut self.curs);
        if res.is_err() {
            self.curs.idx = temp_idx;
        }
        res
    }
}

pub fn _internal_wirewriter_consumed(writer: &WireWriter<'_>) -> usize {
    writer.initial_len - writer.curs.remaining()
}

pub struct VectoredWriter<'a, const E: bool = true> {
    curs: VectoredCursorMut<'a>,
}

impl<'a, const E: bool> VectoredWriter<'a, E> {
    pub fn new(bytes: VectoredBufMut<'a>) -> Self {
        VectoredWriter {
            curs: VectoredCursorMut::new(bytes),
        }
    }

    pub fn advance(&mut self, amount: usize) -> Result<(), WireError> {
        let temp_arr_idx = self.curs.arr_idx;
        let temp_idx = self.curs.idx;
        let res = self.curs.advance(amount);
        if res.is_err() {
            self.curs.arr_idx = temp_arr_idx;
            self.curs.idx = temp_idx;
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

    pub fn finalize_after<T>(
        action: Result<(), WireError>,
        reader: &Self,
    ) -> Result<(), WireError> {
        if action.is_ok() {
            reader.finalize()?;
        }
        action
    }

    pub fn is_empty(&self) -> bool {
        self.curs.is_empty()
    }

    pub fn read<T>(&mut self, writable: &T) -> Result<(), WireError>
    where
        T: VectoredWrite,
    {
        let temp_arr_idx = self.curs.arr_idx;
        let temp_idx = self.curs.idx;
        let res = writable.write_vectored::<E>(&mut self.curs);
        if res.is_err() {
            self.curs.arr_idx = temp_arr_idx;
            self.curs.idx = temp_idx;
        }
        res
    }

    pub fn read_partial<T, const L: usize>(&mut self, writable: &T) -> Result<(), WireError>
    where
        T: VectoredWritePart,
    {
        let temp_arr_idx = self.curs.arr_idx;
        let temp_idx = self.curs.idx;
        let res = writable.write_vectored_part::<L, E>(&mut self.curs);
        if res.is_err() {
            self.curs.arr_idx = temp_arr_idx;
            self.curs.idx = temp_idx;
        }
        res
    }
}

pub fn _internal_vectoredwriter_vec_index(writer: &VectoredWriter) -> usize {
    writer.curs.wire.len().saturating_sub(writer.curs.arr_idx)
}

pub fn _internal_vectoredwriter_slice_index(writer: &VectoredWriter) -> usize {
    writer.curs.idx
}

impl WireWrite for str {
    fn write_wire<'a, const E: bool>(&self, curs: &mut WireCursorMut<'a>) -> Result<(), WireError> {
        curs.put_slice(self.as_bytes())
    }
}

impl VectoredWrite for str {
    fn write_vectored<'a, const E: bool>(
        &self,
        curs: &mut VectoredCursorMut<'a>,
    ) -> Result<(), WireError> {
        curs.put_slice(self.as_bytes())
    }
}

impl WireWrite for [u8] {
    fn write_wire<'a, const E: bool>(&self, curs: &mut WireCursorMut<'a>) -> Result<(), WireError> {
        curs.put_slice(self)
    }
}

impl VectoredWrite for [u8] {
    fn write_vectored<'a, const E: bool>(
        &self,
        curs: &mut VectoredCursorMut<'a>,
    ) -> Result<(), WireError> {
        curs.put_slice(self)
    }
}

macro_rules! derive_wire_writable {
    ($int:ty)=> {
        impl WireWrite for $int {
            fn write_wire<const E: bool>(&self, curs: &mut WireCursorMut<'_>) -> Result<(), WireError> {
                if E {
                    curs.put_slice(self.to_be_bytes().as_slice())
                } else {
                    curs.put_slice(self.to_le_bytes().as_slice())
                }
            }
        }
    };

    ($i1:ty, $($i2:ty),+) => {
        derive_wire_writable! { $i1 }
        derive_wire_writable! { $($i2),+ }
    };
}

macro_rules! derive_wire_partwritable {
    ($int:ty)=> {
        impl WireWritePart for $int {
            fn write_wire_part<const L: usize, const E: bool>(&self, curs: &mut WireCursorMut<'_>) -> Result<(), WireError> {
                assert!(L < mem::size_of::<$int>()); // TODO: once more powerful const generic expressions are in rust, use them
                if E {
                    curs.put_slice(&self.to_be_bytes().get(..L).unwrap_or(&[])) // TODO: downcast larger array to smaller one here for safety guarantees
                } else {
                    curs.put_slice(&self.to_le_bytes().get(..L).unwrap_or(&[]))
                }
            }
        }
    };

    ($i1:ty, $($i2:ty),+) => {
        derive_wire_partwritable! { $i1 }
        derive_wire_partwritable! { $($i2),+ }
    };
}

macro_rules! derive_vectored_writable {
    ($int:ty)=> {
        impl VectoredWrite for $int {
            fn write_vectored<const E: bool>(&self, curs: &mut VectoredCursorMut<'_>) -> Result<(), WireError> {
                if E {
                    curs.put_slice(self.to_be_bytes().as_slice())
                } else {
                    curs.put_slice(self.to_le_bytes().as_slice())
                }
            }
        }
    };

    ($i1:ty, $($i2:ty),+) => {
        derive_vectored_writable! { $i1 }
        derive_vectored_writable! { $($i2),+ }
    };
}

macro_rules! derive_vectored_partwritable {
    ($int:ty)=> {
        impl VectoredWritePart for $int {
            fn write_vectored_part<const L: usize, const E: bool>(&self, curs: &mut VectoredCursorMut<'_>) -> Result<(), WireError> {
                assert!(L < mem::size_of::<$int>()); // TODO: once more powerful const generic expressions are in rust, use them
                if E {
                    curs.put_slice(&self.to_be_bytes().get(..L).unwrap_or(&[])) // TODO: downcast larger array to smaller one here for safety guarantees
                } else {
                    curs.put_slice(&self.to_le_bytes().get(..L).unwrap_or(&[]))
                }
            }
        }
    };

    ($i1:ty, $($i2:ty),+) => {
        derive_vectored_partwritable! { $i1 }
        derive_vectored_partwritable! { $($i2),+ }
    };
}

derive_wire_writable!(i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, f32, f64, isize, usize);
derive_vectored_writable!(i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, f32, f64, isize, usize);

// No floats or signed integers--their implementations aren't conducive to chopping off bytes at will
derive_wire_partwritable!(u16, u32, u64, u128, usize);
derive_vectored_partwritable!(u16, u32, u64, u128, usize);
