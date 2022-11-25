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

/// Serialization from a data type to the wire.
///
/// A type that implements this trait guarantees that it can be serialized into a
/// number of bytes that will be written to the provided [`WireCursorMut`]. If the
/// bytes cannot be written to the wire, an error will be returned.
pub trait WireWrite {
    /// Serializes the data type into a number of bytes on the wire, or returns a [`WireError`] on failure.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being written. If `E` is set to
    /// `true`, then the data will be serialized in big endian format; if `false`, it will be serialized
    /// in little endian.
    ///
    /// ## Errors
    ///
    /// [`WireError::InsufficientBytes`] - not enough bytes remained on the cursor to write the type to the wire.
    ///
    /// [`WireError::Internal`] - an internal error occurred in the `wire-rs` library
    fn write_wire<const E: bool>(&self, curs: &mut WireCursorMut<'_>) -> Result<(), WireError>;
}

/// Serialization from a data type to a portion of the wire smaller than the full size of the data type.
///
/// A type that implements this trait guarantees that at least a subset of its values can be serialized
/// into a specified number of bytes (greater than zero but less than the size of the type). The serialized
/// bytes are written to the supplied [`WireCursorMut`]. For values that cannot be serialized into the number
/// of bytes specified, the [`WireError::InvalidData`] error should be returned.
///
/// This trait is most useful for writing integer values to the wire that can be represented in fewer bytes
/// than what the data type is capable of storing, such as writing out a `u32` to 3 bytes. The caller must ensure
/// that the value stored in the data type can fit in the number of bytes specified for the operation to succeed.
///
/// Types implementing this trait should also implement [`WireWrite`] for the case where the specified number of bytes
/// is equal to the size of the type.
pub trait WireWritePart: Sized {
    /// Serializes the data type into exactly `L` bytes on the wire. If the data's value exceeds the bounds of
    /// what can be stored in `L` bytes, this function will return a [`WireError::InvalidData`] error.
    ///
    /// As an example, the following function would return an error because the value contained in the
    /// `u16` can't be represented by a single byte:
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
    /// If the `u16` were a value less than or equal to 0xFF, the above function would return an Ok() result.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being written. If `E` is set to
    /// `true`, then the data will be serialized in big endian format; if `false`, it will be serialized in little endian.
    fn write_wire_part<const L: usize, const E: bool>(
        &self,
        curs: &mut WireCursorMut<'_>,
    ) -> Result<(), WireError>;
}

/// Serialization from a data type to the vectored wire.
///
/// A type that implements this trait guarantees that it can be serialized into a
/// number of bytes that will be written to the provided [`VectoredCursorMut`]. If the
/// bytes cannot be written to the vectored wire, an error will be returned.
pub trait VectoredWrite {
    /// Serializes the data type into a number of bytes on the vectored wire, or returns a [`WireError`] on failure.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being written. If `E` is set to
    /// `true`, then the data will be serialized in big endian format; if `false`, it will be serialized
    /// in little endian.
    ///
    /// ## Errors
    ///
    /// [`WireError::InsufficientBytes`] - not enough bytes remained on the cursor to write the type to the wire.
    ///
    /// [`WireError::Internal`] - an internal error occurred in the `wire-rs` library
    fn write_vectored<const E: bool>(
        &self,
        curs: &mut VectoredCursorMut<'_>,
    ) -> Result<(), WireError>;
}

/// Serialization from an owned data type to a portion of the vectored wire smaller than what the data type would
/// normally produce.
///
/// This trait is most useful for writing integer values to the vectored wire that can be represented in fewer bytes
/// than what the data type is capable of storing, such as writing out a `u32` to 3 bytes. The caller must ensure
/// that the value stored in the data type can fit in the number of bytes specified.
///
/// A type implementing this trait must guarantee that any length `L` passed in that is greater than 0 and smaller
/// than the size of the type can be converted into the type. Types implementing this trait should also implement
/// [`WireWrite`] for the case where `L` is equal to the size of the type.
pub trait VectoredWritePart: Sized {
    /// Serializes the data type into `L` bytes on the vectored wire. If the data's value exceeds the bounds of
    /// what can be stored in `L` bytes, this function will return a WireError::InvalidData error.
    ///
    /// As an example, the following function would return an error because the value contained in the
    /// `u16` can't be represented by a single byte:
    ///
    /// ```rust
    /// use wire_rs::{WireWriter, WireError};
    ///
    /// fn decode_partial_out_of_range() -> Result<(), WireError> {
    ///     let mut buf = [0u8; 4];
    ///     let out_of_range = 0x0100u16;
    ///     let mut writer: WireWriter = WireWriter::new(buf.as_mut_slice());
    ///     writer.write_part::<u16, 1>(&out_of_range) // Returns Err(WireError::InvalidData)
    /// }
    /// ```
    ///
    /// If the value were <= 0xFF instead, the above function would return an Ok() result.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being written. If `E` is set to
    /// `true`, then the data will be serialized in big endian format; if `false`, it will be serialized in little endian.
    fn write_vectored_part<const L: usize, const E: bool>(
        &self,
        curs: &mut VectoredCursorMut<'_>,
    ) -> Result<(), WireError>;
}

/// A cursor that acts as an index over a mutable slice and provides operations to sequentially
/// write data to it.
///
/// When implementing the [`WireWrite`] trait or one of its variants, this cursor provides an
/// interface for writing data to the wire. When an error is returned by the cursor, it
/// should be returned by the trait method being implemented. This can be easily accomplished
/// using the `?` operator.
///
/// NOTE: this is an internal structure, and is NOT meant to be used to write data from a wire
/// in the same manner as a [`WireWriter`]. A `WireWriter` is guaranteed to maintain the index
/// of its last succesful write if any of its methods return an error, while this cursor may move its
/// internal index forward by some unspecified amount when an error is encountered.
pub struct WireCursorMut<'a> {
    wire: &'a mut [u8],
    idx: usize,
}

impl<'a> WireCursorMut<'a> {
    /// Create a `WireCursorMut` that writes to the given slice `wire`.
    fn new(wire: &'a mut [u8]) -> Self {
        WireCursorMut { wire, idx: 0 }
    }

    /// Advance the cursor's index by the given amount, returning an error if
    /// there are insufficient bytes on the wire.
    pub fn advance(&mut self, amount: usize) -> Result<(), WireError> {
        self.idx = match self.idx.checked_add(amount) {
            Some(new_idx) if new_idx > self.wire.len() => return Err(WireError::InsufficientBytes),
            Some(new_idx) => new_idx,
            None => return Err(WireError::InsufficientBytes),
        };

        Ok(())
    }

    /// Advance the cursor's index by the given amount, or to the end of the wire if
    /// the amount exceeds the number of remaining bytes.
    pub fn advance_up_to(&mut self, amount: usize) {
        self.idx = match self.idx.checked_add(amount) {
            Some(new_idx) => cmp::min(new_idx, self.wire.len()),
            None => self.wire.len(),
        };
    }

    /// Check whether the vectored wire has any remaining bytes that can be written
    /// to by the cursor.
    pub fn is_empty(&self) -> bool {
        self.wire.is_empty()
    }

    /// Write a slice of bytes to the wire.
    pub fn put_slice(&mut self, slice: &[u8]) -> Result<(), WireError> {
        let tmp_slice = match self.wire.get_mut(self.idx..) {
            Some(s) => s,
            None => return Err(WireError::Internal), // Invariant: the index should never exceed the bound of the slice
        };

        if tmp_slice.len() < slice.len() {
            return Err(WireError::InsufficientBytes);
        }

        for (a, b) in tmp_slice.iter_mut().zip(slice.iter()) {
            *a = *b;
        }

        self.idx += slice.len(); // tmp_slice.len() >= slice.len, so self.idx + slice.len() <= self.wire.len()
        Ok(())
    }

    /// Serialize a given type `T` that implements the [`WireWrite`] trait to the wire.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being written. If `E` is set to
    /// `true`, then the data will be serialized in big endian format; if `false`, it will be serialized
    /// in little endian.
    pub fn put_writable<T, const E: bool>(&mut self, writable: &T) -> Result<(), WireError>
    where
        T: WireWrite + ?Sized,
    {
        writable.write_wire::<E>(self)
    }

    /// Serialize `L` bytes to the wire from a given type `T` that implements the
    /// [`WireWritePart`] trait.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being written. If `E` is set to
    /// `true`, then the data will be serialized in big endian format; if `false`, it will be serialized
    /// in little endian.
    pub fn put_writable_part<T, const L: usize, const E: bool>(
        &mut self,
        writable: &T,
    ) -> Result<(), WireError>
    where
        T: WireWritePart,
    {
        writable.write_wire_part::<L, E>(self)
    }

    /// Get the number of bytes remaining on the wire for the given cursor.
    pub fn remaining(&self) -> usize {
        self.wire.len().saturating_sub(self.idx)
    }
}

/// A cursor that acts as an index over a set of vectored mutable slices and provides
/// operations to sequentially write data to the slices.
///
/// When implementing the [`VectoredWrite`] trait or one of its variants, this cursor provides an
/// interface for writing data to the vectored wire. When an error is returned by the cursor, it
/// should be returned by the trait method being implemented. This can be easily accomplished
/// using the `?` operator.
///
/// NOTE: this is an internal structure, and is NOT meant to be used to write data from a wire
/// in the same manner as a [`WireWriter`]. A `WireWriter` is guaranteed to maintain the index
/// of its last succesful write if any of its methods return an error, while this cursor may move its
/// internal index forward by some unspecified amount when an error is encountered.
pub struct VectoredCursorMut<'a> {
    wire: VectoredBufMut<'a>,
    arr_idx: usize,
    idx: usize,
}

impl<'a> VectoredCursorMut<'a> {
    /// Create a `VectoredCursorMut` that writes to the given set of vectored slices `wire`.
    fn new(wire: VectoredBufMut<'a>) -> Self {
        VectoredCursorMut {
            wire,
            arr_idx: 0,
            idx: 0,
        }
    }

    /// Advance the cursor's index by the given amount, returning an error if there are insufficient bytes
    /// on the vectored wire.
    pub fn advance(&mut self, mut amount: usize) -> Result<(), WireError> {
        while let Some(curr_slice) = self.wire.get(self.arr_idx) {
            let remaining_slice_len = match curr_slice.len().checked_sub(self.idx) {
                None => return Err(WireError::Internal), // Invariant: the index should never exceed the bound of the slice
                Some(0) => {
                    if self.wire.get(self.arr_idx + 1).is_none() {
                        return Err(WireError::InsufficientBytes);
                    }

                    self.arr_idx += 1; // Checked above to ensure that self.wire[self.arr_idx + 1] exists
                    self.idx = 0;
                    continue;
                }
                Some(l) => l,
            };

            match amount.checked_sub(remaining_slice_len) {
                None | Some(0) => {
                    // Invariant: cannot overflow (as you cannot have a slice greater than `usize::MAX`)
                    self.idx += amount; // amount <= curr_slice.len() - self.idx -> self.idx + amount <= curr_slice.len()
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

    /// Advance the cursor's index by the given amount, or to the end of the vectored wire if the amount
    /// exceeds the number of remaining bytes.
    pub fn advance_up_to(&mut self, mut amount: usize) {
        while let Some(curr_slice) = self.wire.get(self.arr_idx) {
            let remaining_slice_len = match curr_slice.len().checked_sub(self.idx) {
                None | Some(0) => {
                    // Invariant: None should never occur, as the index should never exceed the bound of the first slice
                    if self.wire.get(self.arr_idx + 1).is_none() {
                        return;
                    }
                    self.arr_idx += 1; // Checked above to ensure that self.wire[self.arr_idx + 1] exists
                    self.idx = 0;
                    continue;
                }
                Some(l) => l,
            };

            match amount.checked_sub(remaining_slice_len) {
                Some(0) | None => {
                    // Invariant: cannot overflow (as you cannot have a slice greater than `usize::MAX`)
                    self.idx += amount; // amount < curr_slice.len() - self.idx -> self.idx + amount <= curr_slice.len()
                    return;
                }
                Some(new_amount) => {
                    if self.wire.get(self.arr_idx + 1).is_none() {
                        self.idx = curr_slice.len();
                        return;
                    }
                    self.arr_idx += 1; // Checked above to ensure that self.wire[self.arr_idx + 1] exists
                    self.idx = 0;
                    amount = new_amount;
                }
            }
        }
    }

    /// Check whether the vectored wire has any remaining bytes that can be written to by the cursor.
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

    /// Write a slice of bytes to the wire.
    pub fn put_slice(&mut self, mut slice: &[u8]) -> Result<(), WireError> {
        while let Some(curr_slice) = self.wire.get_mut(self.arr_idx) {
            let wire_remaining = match curr_slice.get_mut(self.idx..) {
                Some(s) => s,
                None => return Err(WireError::Internal), // Invariant: the index can never exceed the bound of the slice
            };

            for (a, b) in wire_remaining.iter_mut().zip(slice.iter()) {
                *a = *b;
            }

            let num_read = cmp::min(wire_remaining.len(), slice.len());
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
                    self.arr_idx += 1; // Checked above to ensure that self.wire[self.arr_idx + 1] exists
                    self.idx = 0;
                }
                None => return Err(WireError::Internal), // Invariant: num_read cannot exceed slice.len()
            }
        }

        Err(WireError::InsufficientBytes)
    }

    /// Serialize a given type `T` that implements the [`WireWrite`] trait to the wire.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being written. If `E` is set to
    /// `true`, then the data will be serialized in big endian format; if `false`, it will be serialized
    /// in little endian.
    pub fn put_writable<T, const E: bool>(&mut self, writable: &T) -> Result<(), WireError>
    where
        T: VectoredWrite + ?Sized,
    {
        writable.write_vectored::<E>(self)
    }

    /// Serialize `L` bytes to the wire from a given type `T` that implements the [`WireWritePart`]
    /// trait.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being written. If `E` is set to
    /// `true`, then the data will be serialized in big endian format; if `false`, it will be serialized
    /// in little endian.
    pub fn put_writable_part<T, const L: usize, const E: bool>(
        &mut self,
        writable: &T,
    ) -> Result<(), WireError>
    where
        T: VectoredWritePart,
    {
        writable.write_vectored_part::<L, E>(self)
    }

    /// Get the number of bytes remaining on the wire for the given cursor.
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
    /// Create a `WireWriter` that can write data types sequentially to the `bytes` slice.
    pub fn new(bytes: &'a mut [u8]) -> Self {
        let initial_len = bytes.len();
        WireWriter {
            curs: WireCursorMut::new(bytes),
            initial_len,
        }
    }

    /// Advance the writer's index forward by the given amount of bytes, returning an error if there are insufficient
    /// bytes on the wire to do so.
    pub fn advance(&mut self, amount: usize) -> Result<(), WireError> {
        let prev_idx = self.curs.idx;
        let res = self.curs.advance(amount);
        if res.is_err() {
            self.curs.idx = prev_idx;
        }
        res
    }

    /// Advance the writer's index forward by the given number of bytes, or to the end of the wire if the amount
    /// exceeds the number of remaining bytes.
    pub fn advance_up_to(&mut self, amount: usize) {
        self.curs.advance_up_to(amount);
    }

    /// Check if the writer has no more bytes left on the wire that can be written to. If any
    /// bytes remain, return [`WireError::ExtraBytes`]; otherwise, return Ok().
    pub fn finalize(&self) -> Result<(), WireError> {
        if !self.is_empty() {
            Err(WireError::ExtraBytes)
        } else {
            Ok(())
        }
    }

    /// Check if the writer has no more bytes left on the wire that can be written to after
    /// the given action. If any bytes remain, return [`WireError::ExtraBytes`]; otherwise,
    /// return Ok().
    pub fn finalize_after<T>(
        action: Result<(), WireError>,
        reader: &Self,
    ) -> Result<(), WireError> {
        if action.is_ok() {
            reader.finalize()?;
        }
        action
    }

    /// Check whether the writer has any remaining bytes that can be written to.
    pub fn is_empty(&self) -> bool {
        self.curs.is_empty()
    }

    /// Write the given data type `writable` to the wire.
    pub fn write<T>(&mut self, writable: &T) -> Result<(), WireError>
    where
        T: WireWrite + ?Sized,
    {
        let temp_idx = self.curs.idx;
        let res = writable.write_wire::<E>(&mut self.curs);
        if res.is_err() {
            self.curs.idx = temp_idx;
        }
        res
    }

    /// Write the given data type `writable` to `L` bytes on the wire.
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
    /// Create a `VectoredWriter` that can write data types sequentially to the vectored `bytes` slice.
    pub fn new(bytes: VectoredBufMut<'a>) -> Self {
        VectoredWriter {
            curs: VectoredCursorMut::new(bytes),
        }
    }

    /// Advance the writer's index forward by the given amount of bytes, returning an error if there are insufficient
    /// bytes on the wire to do so.
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

    /// Advance the writer's index forward by the given number of bytes, or to the end of the vectored
    /// wire if the amount exceeds the number of remaining bytes.
    pub fn advance_up_to(&mut self, index: usize) {
        self.curs.advance_up_to(index);
    }

    /// Check if the writer has no more bytes left on the vectored wire that can be written
    /// to. If any bytes remain, return [`WireError::ExtraBytes`]; otherwise, return Ok().
    pub fn finalize(&self) -> Result<(), WireError> {
        if self.is_empty() {
            Ok(())
        } else {
            Err(WireError::ExtraBytes)
        }
    }

    /// Check if the writer has no more bytes left on the vectored wire that can be written
    /// to after the given action. If any bytes remain, return [`WireError::ExtraBytes`];
    /// otherwise, return Ok().
    pub fn finalize_after<T>(
        action: Result<(), WireError>,
        reader: &Self,
    ) -> Result<(), WireError> {
        if action.is_ok() {
            reader.finalize()?;
        }
        action
    }

    /// Check whether the writer has any remaining bytes that can be written to.
    pub fn is_empty(&self) -> bool {
        self.curs.is_empty()
    }

    /// Write the given data type `writable` to the vectored wire.
    pub fn write<T>(&mut self, writable: &T) -> Result<(), WireError>
    where
        T: VectoredWrite + ?Sized,
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

    /// Write the given data type `writable` to `L` bytes on the vectored wire.
    pub fn write_part<T, const L: usize>(&mut self, writable: &T) -> Result<(), WireError>
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
