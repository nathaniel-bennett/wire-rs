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
pub type VectoredBuf<'a> = &'a [io::IoSlice<'a>];
#[cfg(not(feature = "ioslice"))]
pub type VectoredBuf<'a> = &'a [&'a [u8]];

/// Deserialization to an owned data type from the wire.
///
/// A type that implements this trait guarantees that it can be constructed using a
/// number of bytes from the provided [`WireCursor`]. If the bytes contained on the wire
/// would lead to the construction of an invalid instance of the object, an error will
/// be returned instead of the object.
pub trait WireRead: Sized {
    /// Consumes a number of bytes from `curs` and returns an owned instance of the specified type,
    /// or returns a [`WireError`] on failure.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being read. If `E` is set to
    /// `true`, then the data will be deserialized in big endian format; if `false`, it will be deserialized
    /// in little endian.
    ///
    /// ## Errors
    ///
    /// [`WireError::InsufficientBytes`] - not enough bytes remained on the cursor to construct the type.
    ///
    /// [`WireError::InvalidData`] - the bytes retrieved from `curs` could not be used to construct a valid instance
    /// of the type.
    ///
    /// [`WireError::Internal`] - an internal error occurred in the `wire-rs` library
    fn read_wire<const E: bool>(curs: &mut WireCursor<'_>) -> Result<Self, WireError>;

    // Add once try_from_fn is stabilized
    /*
    fn array_from_wire<const L: usize, const E: bool>(curs: &mut WireCursor<'_>) -> Result<[Self; L], WireError> {
        std::array::try_from_fn(|_| { Self::from_wire::<E>(curs) })
    }
    */
}

/// Deserialization to a composite data type (i.e. containing both owned structures and
/// references) from the wire.
///
/// A type that implements this trait guarantees that it can be constructed using a
/// number of bytes from the provided [`WireCursor`]. If the bytes contained on the wire
/// would lead to the construction of an invalid instance of the object, an error will
/// be returned instead of the object.
pub trait WireReadComp<'a>: Sized {
    /// Consumes a number of bytes from `curs` and returns an owned instance of the specified type,
    /// or returns a [`WireError`] on failure.
    ///
    /// The returned instance must not outlive the lifetime of the buffer that it was constructed from,
    /// though it may outlive the `WireReader` used to construct it.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being read. If `E` is set to
    /// `true`, then the data will be deserialized in big endian format; if `false`, it will be deserialized
    /// in little endian.
    ///
    /// ## Errors
    ///
    /// [`WireError::InsufficientBytes`] - not enough bytes remained on the cursor to construct the type.
    ///
    /// [`WireError::InvalidData`] - the bytes retrieved from `curs` could not be used to construct a valid instance
    /// of the type.
    ///
    /// [`WireError::Internal`] - an internal error occurred in the `wire-rs` library
    fn read_wire_comp<const E: bool>(curs: &mut WireCursor<'a>) -> Result<Self, WireError>;

    // Add once try_from_fn is stabilized
    /*
    fn array_from_wire<const L: usize, const E: bool>(curs: &mut WireCursor<'_>) -> Result<[Self; L], WireError> {
        std::array::try_from_fn(|_| { Self::from_wire::<E>(curs) })
    }
    */
}

/// Deserialization to an owned data type from a portion of the wire smaller than what the data type would normally consume.
///
/// A type that implements this trait guarantees that it can be constructed using a specified
/// number of bytes (greater than zero but less than the size of the type) from the provided
/// [`WireCursor`]. If the bytes contained on the wire would lead to the construction of an
/// invalid instance of the object, an error will be returned instead of the object.
///
/// This trait is most useful for reading integer values from the wire that are represented in fewer bytes than the data type,
/// such as reading in 3 bytes to form a u32 or 5 bytes to form a u64.
///
/// Types implementing this trait should additionally implement [`WireRead`] for
/// the case where `L` is equal to the size of the type.
pub trait WireReadPart: Sized {
    /// Consumes exactly `L` bytes (where 0 < `L` < size_of(type)) from `curs` and returns an owned
    /// instance of the specified type, or returns a [`WireError`] on failure.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being read. If `E` is set to
    /// `true`, then the data will be deserialized in big endian format; if `false`, it will be deserialized
    /// in little endian.
    ///
    /// ## Errors
    ///
    /// [`WireError::InsufficientBytes`] - not enough bytes remained on the cursor to construct the type.
    ///
    /// [`WireError::InvalidData`] - the bytes retrieved from `curs` could not be used to construct a
    /// valid instance of the type.
    ///
    /// [`WireError::Internal`] - an internal error occurred in the `wire-rs` library
    fn read_wire_part<const L: usize, const E: bool>(
        curs: &mut WireCursor<'_>,
    ) -> Result<Self, WireError>;
}

/// Deserialization to an immutable reference of a data type from the wire.
///
/// A type that implements this trait guarantees that it can be constructed using a given
/// number of bytes from the provided [`WireCursor`]. If the bytes contained on the wire
/// cannot be converted into a reference of a valid instance of the object, an error will
/// be returned instead of the reference.
pub trait WireReadRef {
    /// Consumes exactly `size` bytes from `curs` and returns an immutable reference of the specified type,
    /// or returns a [`WireError`] on failure.
    ///
    /// The returned reference must not outlive the lifetime of the buffer that it references,
    /// though it may outlive the [`WireReader`] used to construct it.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being read. If `E` is set to
    /// `true`, then the data will be deserialized in big endian format; if `false`, it will be deserialized
    /// in little endian.
    ///
    /// ## Errors
    ///
    /// [`WireError::InsufficientBytes`] - less than `size` bytes remained on the cursor.
    ///
    /// [`WireError::InvalidData`] - the bytes retrieved from `curs` could not be used to construct a valid
    /// reference of the type.
    ///
    /// [`WireError::Internal`] - an internal error occurred in the `wire-rs` library
    fn read_wire_ref<'a>(curs: &mut WireCursor<'a>, size: usize) -> Result<&'a Self, WireError>;
}

/// Deserialization to an owned data type from the vectored wire.
///
/// A type that implements this trait guarantees that it can be constructed using a
/// number of bytes from the provided [`VectoredCursor`]. If the bytes contained on the
/// vectored wire would lead to the construction of an invalid instance of the object,
/// an error will be returned instead of the object.
pub trait VectoredRead: Sized {
    /// Consumes a number of bytes from `curs` and returns an owned instance of the specified type,
    /// or returns a [`WireError`] on failure.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being read. If `E` is set to
    /// `true`, then the data will be deserialized in big endian format; if `false`, it will be deserialized
    /// in little endian.
    ///
    /// ## Errors
    ///
    /// [`WireError::InsufficientBytes`] - not enough bytes remained on the vectored cursor to construct
    /// the type.
    ///
    /// [`WireError::InvalidData`] - the bytes retrieved from `curs` could not be used to construct a
    /// valid instance of the type.
    ///
    /// [`WireError::Internal`] - an internal error occurred in the `wire-rs` library
    fn read_vectored<const E: bool>(curs: &mut VectoredCursor<'_>) -> Result<Self, WireError>;

    /*
    fn array_from_vectored<const L: usize, const E: bool>(curs: &mut VectoredCursor<'_>) -> Result<[Self; L], WireError> {
        std::array::try_from_fn(|_| { Self::from_vectored::<E>(curs) })
    }
    */
}

/// Deserialization to an owned data type from a portion of the vectored wire smaller than what
/// the data type would normally consume.
///
/// A type that implements this trait guarantees that it can be constructed using a specified
/// number of bytes (greater than zero but less than the size of the type) from the provided
/// [`VectoredCursor`]. If the bytes contained on the vectored wire would lead to the construction of an
/// invalid instance of the object, an error will be returned instead of the object.
///
/// This trait is most useful for reading integer values from the vectored wire that are represented in fewer bytes than the data type,
/// such as reading in 3 bytes to form a u32 or 5 bytes to form a u64.
///
/// Types implementing this trait should additionally implement [`VectoredRead`] for
/// the case where `L` is equal to the size of the type.
pub trait VectoredReadPart: Sized {
    /// Consumes exactly `L` bytes (where 0 < `L` < size_of(`type`)) from `curs` and returns an owned
    /// instance of the specified type, or returns a [`WireError`] on failure.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being read. If `E` is set to
    /// `true`, then the data will be deserialized in big endian format; if `false`, it will be deserialized
    /// in little endian.
    ///
    /// ## Errors
    ///
    /// [`WireError::InsufficientBytes`] - not enough bytes remained on the cursor to construct the type.
    ///
    /// [`WireError::InvalidData`] - the bytes retrieved from `curs` could not be used to construct a
    /// valid instance of the type.
    ///
    /// [`WireError::Internal`] - an internal error occurred in the `wire-rs` library
    fn read_vectored_part<const L: usize, const E: bool>(
        curs: &mut VectoredCursor<'_>,
    ) -> Result<Self, WireError>;
}

/// Deserialization to a composite data type (i.e. containing both owned structures and
/// references) from the vectored wire.
///
/// A type that implements this trait guarantees that it can be constructed using a
/// number of bytes from the provided [`VectoredCursor`]. If the bytes contained on the
/// vectored wire would lead to the construction of an invalid instance of the object,
/// an error will be returned instead of the object.
pub trait VectoredReadComp<'a>: Sized {
    /// Consumes a number of bytes from `curs` and returns an owned instance of the specified
    /// type, or returns a [`WireError`] on failure.
    ///
    /// The returned instance must not outlive the lifetime of the vectored buffer that it was
    /// constructed from, though it may outlive the `VectoredReader` used to construct it.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being read. If
    /// `E` is set to `true`, then the data will be deserialized in big endian format; if
    /// `false`, it will be deserialized in little endian.
    ///
    /// ## Errors
    ///
    /// [`WireError::InsufficientBytes`] - not enough bytes remained on the cursor to construct
    /// the type.
    ///
    /// [`WireError::InvalidData`] - the bytes retrieved from `curs` could not be used to
    /// construct a valid instance of the type.
    ///
    /// [`WireError::Internal`] - an internal error occurred in the `wire-rs` library
    fn read_vectored_comp<const E: bool>(curs: &mut VectoredCursor<'a>) -> Result<Self, WireError>;

    // Add once try_from_fn is stabilized
    /*
    fn array_from_wire<const L: usize, const E: bool>(curs: &mut WireCursor<'_>) -> Result<[Self; L], WireError> {
        std::array::try_from_fn(|_| { Self::from_wire::<E>(curs) })
    }
    */
}

/// Deserialization to an immutable reference of a data type from the vectored wire.
///
/// A type that implements this trait guarantees that it can be constructed using a given
/// number of bytes from the provided [`VectoredCursor`]. If the bytes contained on the
/// vectored wire cannot be converted into a reference of a valid instance of the object,
/// an error will be returned instead of the reference.
pub trait VectoredReadRef {
    /// Consumes exactly `size` bytes from `curs` and returns an immutable reference of the specified type,
    /// or returns a [`WireError`] on failure.
    ///
    /// The returned reference must not outlive the lifetime of the vectored buffer that it references,
    /// though it may outlive the [`VectoredReader`] used to construct it.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being read. If `E` is set to
    /// `true`, then the data will be deserialized in big endian format; if `false`, it will be deserialized
    /// in little endian.
    ///
    /// ## Errors
    ///
    /// [`WireError::InsufficientBytes`] - less than `size` bytes remained on the cursor.
    ///
    /// [`WireError::InvalidData`] - the bytes retrieved from `curs` could not be used to construct a
    /// valid reference of the type.
    ///
    /// [`WireError::Internal`] - an internal error occurred in the `wire-rs` library
    fn read_vectored_ref<'a>(
        curs: &mut VectoredCursor<'a>,
        size: usize,
    ) -> Result<&'a Self, WireError>;
}

/// A cursor that acts as an index over a contiguous immutable slice and provides operations
/// to sequentially read data from it.
///
/// When implementing the [`WireRead`] trait or one of its variants, this cursor provides an
/// interface for reading data from the wire. When an error is returned by the cursor, it
/// should be returned by the trait method being implemented. This can be easily accomplished
/// using the `?` operator.
///
/// NOTE: this is an internal structure, and is NOT meant to be used to read data from a wire
/// in the same manner as a [`WireReader`]. A `WireReader` is guaranteed to maintain the index
/// of its last succesful read if any of its methods return an error, while this cursor may move
/// its internal index forward by some unspecified amount when an error is encountered.
#[derive(Clone, Copy)]
pub struct WireCursor<'a> {
    wire: &'a [u8],
}

impl<'a> WireCursor<'a> {
    /// Create a `WireCursor` that reads from the given slice `wire`.
    fn new(wire: &'a [u8]) -> Self {
        WireCursor { wire }
    }

    /// Advance the cursor's index by the given amount, returning an error if there are
    /// insufficient bytes on the wire.
    pub fn advance(&mut self, amount: usize) -> Result<(), WireError> {
        self.wire = match self.wire.get(amount..) {
            Some(w) => w,
            None => return Err(WireError::InsufficientBytes),
        };
        Ok(())
    }

    /// Advance the cursor's index by the given amount, or to the end of the wire if
    /// the amount exceeds the number of remaining bytes.
    pub fn advance_up_to(&mut self, amount: usize) {
        self.wire = match self.wire.get(amount..) {
            Some(w) => w,
            None => &[],
        };
    }

    /// Retrieve a reference to an array of bytes of size `L` from the wire.
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

    /// Deserialize a given type `T` that implements the [`WireRead`] trait from the wire, and
    /// return an owned instance of it.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being read. If `E` is set to
    /// `true`, then the data will be deserialized in big endian format; if `false`, it will be deserialized
    /// in little endian.
    pub fn get_readable<T, const E: bool>(&mut self) -> Result<T, WireError>
    where
        T: WireRead,
    {
        T::read_wire::<E>(self)
    }

    /// Deserialize `L` bytes from the wire into a given type `T` that implements the [`WireReadPart`]
    /// trait, and return an owned instance of it.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being read. If `E` is set to
    /// `true`, then the data will be deserialized in big endian format; if `false`, it will be deserialized
    /// in little endian.
    pub fn get_readable_part<T, const L: usize, const E: bool>(&mut self) -> Result<T, WireError>
    where
        T: WireReadPart,
    {
        T::read_wire_part::<L, E>(self)
    }

    /// Deserialize a given type `T` that implements the [`WireReadRef`] trait from the wire, and return a
    /// reference to it.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being read. If `E` is set to
    /// `true`, then the data will be deserialized in big endian format; if `false`, it will be deserialized
    /// in little endian.
    pub fn get_readable_ref<T, const E: bool>(&mut self, length: usize) -> Result<&'a T, WireError>
    where
        T: WireReadRef + ?Sized,
    {
        T::read_wire_ref(self, length)
    }

    /// Deserialize a given type `T` that implements the [`WireReadComp`] trait from the wire, and return
    /// an owned instance of it.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being read. If `E` is set to
    /// `true`, then the data will be deserialized in big endian format; if `false`, it will be deserialized
    /// in little endian.
    pub fn get_readable_comp<T, const E: bool>(&mut self) -> Result<T, WireError>
    where
        T: WireReadComp<'a> + ?Sized,
    {
        T::read_wire_comp::<E>(self)
    }

    /// Retrieve a slice of bytes from the wire.
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

    /// Check whether the wire has any remaining bytes that can be read by the cursor.
    pub fn is_empty(&self) -> bool {
        self.wire.is_empty()
    }

    /// Get the number of bytes remaining on the wire for the given cursor.
    pub fn remaining(&self) -> usize {
        self.wire.len()
    }
}

/// A cursor that acts as an index over a set of vectored immutable slices and provides
/// operations to sequentially read data from the slices.
///
/// When implementing the [`VectoredRead`] trait or one of its variants, this cursor provides an
/// interface for reading data from the vectored wire. When an error is returned by the cursor, it
/// should be returned by the trait method being implemented. This can be easily accomplished
/// using the `?` operator.
///
/// NOTE: this is an internal structure, and is NOT meant to be used to read data from a wire
/// in the same manner as a [`WireReader`]. A `WireReader` is guaranteed to maintain the index
/// of its last succesful read if any of its methods return an error, while this cursor may move its
/// internal index forward by some unspecified amount when an error is encountered.
#[derive(Clone, Copy)]
pub struct VectoredCursor<'a> {
    wire: VectoredBuf<'a>,
    idx: usize,
}

impl<'a> VectoredCursor<'a> {
    /// Create a `VectoredCursor` that reads from the given set of vectored slices `wire`.
    fn new(wire: VectoredBuf<'a>) -> Self {
        VectoredCursor { wire, idx: 0 }
    }

    /// Advance the cursor's index by the given amount, returning an error if there are insufficient bytes
    /// on the vectored wire.
    pub fn advance(&mut self, mut amount: usize) -> Result<(), WireError> {
        while let Some((first, next_slices)) = self.wire.split_first() {
            let remaining_slice_len = match first.len().checked_sub(self.idx) {
                None | Some(0) => {
                    // Invariant: None should never occur, as the index should never exceed the bound of the first slice
                    if next_slices.is_empty() {
                        return Err(WireError::InsufficientBytes);
                    }

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

    /// Advance the cursor's index by the given amount, or to the end of the vectored wire if the amount
    /// exceeds the number of remaining bytes.
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

    /// Check whether the vectored wire has any remaining bytes that can be read by the cursor.
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

    /// Retrieve a the next available byte from the wire.
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

    /// Deserialize a given type `T` that implements the [`VectoredRead`] trait from the vectored wire,
    /// and return an owned instance of it.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being read. If `E` is set to
    /// `true`, then the data will be deserialized in big endian format; if `false`, it will be deserialized
    /// in little endian.
    pub fn get_readable<T, const E: bool>(&mut self) -> Result<T, WireError>
    where
        T: VectoredRead,
    {
        T::read_vectored::<E>(self)
    }

    /// Deserialize `L` bytes from the vectored wire into a given type `T` that implements the
    /// [`VectoredReadPart`] trait, and return an owned instance of it.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being read. If `E` is set to
    /// `true`, then the data will be deserialized in big endian format; if `false`, it will be deserialized
    /// in little endian.
    pub fn get_readable_part<T, const L: usize, const E: bool>(&mut self) -> Result<T, WireError>
    where
        T: VectoredReadPart,
    {
        T::read_vectored_part::<L, E>(self)
    }

    /// Deserialize a given type `T` that implements the [`VectoredReadRef`] trait from the vectored
    /// wire, and return a reference to it.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being read. If `E` is set to
    /// `true`, then the data will be deserialized in big endian format; if `false`, it will be deserialized
    /// in little endian.
    pub fn get_readable_ref<T, const E: bool>(&mut self, length: usize) -> Result<&'a T, WireError>
    where
        T: VectoredReadRef + ?Sized,
    {
        T::read_vectored_ref(self, length)
    }

    /// Deserialize a given type `T` that implements the [`VectoredReadComp`] trait from the wire, and return
    /// an owned instance of it.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being read. If `E` is set to
    /// `true`, then the data will be deserialized in big endian format; if `false`, it will be deserialized
    /// in little endian.
    pub fn get_readable_comp<T, const E: bool>(&mut self) -> Result<T, WireError>
    where
        T: VectoredReadComp<'a> + ?Sized,
    {
        T::read_vectored_comp::<E>(self)
    }

    /// Get the number of bytes remaining on the vectored wire for the given cursor.
    pub fn remaining(&self) -> usize {
        self.wire
            .iter()
            .map(|s| s.len())
            .sum::<usize>()
            .saturating_sub(self.idx)
    }

    /// Attempt to retrieve a contiguous slice of bytes from the wire, returning `None`
    /// if the next `amount` bytes are not all located on the same slice.
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

    /// Attempt to retrieve a reference to a contiguous array of bytes of size `L` from the wire,
    /// returning `None` if the next `L` bytes are not all located on the same slice.
    pub fn try_get_array<const L: usize>(&mut self) -> Option<&'a [u8; L]> {
        match self.try_get(L) {
            Some(arr) => arr.try_into().ok(), // Invariant: should always be Ok
            None => None,
        }
    }
}

/// A wrapper around a `&[u8]` slice that provides an easy interface for reading data types
/// from the slice.
#[derive(Clone, Copy)]
pub struct WireReader<'a, const E: bool = true> {
    curs: WireCursor<'a>,
    initial_len: usize,
}

impl<'a, const E: bool> WireReader<'a, E> {
    /// Create a `WireReader` that can read data types sequentially from the `bytes` slice.
    ///
    /// The generic boolean `E` designates the intended endianness of the data being read. If `E` is set to
    /// `true`, then the data will be deserialized in big endian format; if `false`, it will be deserialized
    /// in little endian. If unset, this will default to `true`, or big endian.
    pub fn new(bytes: &'a [u8]) -> Self {
        WireReader {
            curs: WireCursor::new(bytes),
            initial_len: bytes.len(),
        }
    }

    /// Advance the reader's index forward by the given amount of bytes, returning an error if there are insufficient
    /// bytes on the wire to do so.
    pub fn advance(&mut self, amount: usize) -> Result<(), WireError> {
        let mut temp_curs = self.curs;
        let res = temp_curs.advance(amount);
        if res.is_ok() {
            self.curs = temp_curs;
        }
        res
    }

    /// Advance the reader's index forward by the given number of bytes, or to the end of the wire if the amount
    /// exceeds the number of remaining bytes.
    pub fn advance_up_to(&mut self, amount: usize) {
        self.curs.advance_up_to(amount);
    }

    /// Check if the reader has no more bytes left on the wire that can be read. If any
    /// bytes remain, return [`WireError::ExtraBytes`]; otherwise, return Ok().
    pub fn finalize(&self) -> Result<(), WireError> {
        if !self.is_empty() {
            Err(WireError::ExtraBytes)
        } else {
            Ok(())
        }
    }

    /// Check if the reader has no more bytes left on the wire that can be read after
    /// the given action. If any bytes remain, return [`WireError::ExtraBytes`]; otherwise, return Ok().
    pub fn finalize_after<T>(action: Result<T, WireError>, reader: &Self) -> Result<T, WireError> {
        if action.is_ok() {
            reader.finalize()?;
        }
        action
    }

    /// Check whether the reader has any remaining bytes to be read.
    pub fn is_empty(&self) -> bool {
        self.curs.is_empty()
    }

    /// Read the given data type `T` from the wire without advancing the
    /// index of the reader.
    pub fn peek<T>(&self) -> Result<T, WireError>
    where
        T: WireRead,
    {
        let mut temp_curs = self.curs;
        T::read_wire::<E>(&mut temp_curs)
    }

    /// Read the given data type `T` from the wire without advancing the
    /// index of the reader.
    pub fn peek_comp<T>(&self) -> Result<T, WireError>
    where
        T: WireReadComp<'a>,
    {
        let mut temp_curs = self.curs;
        T::read_wire_comp::<E>(&mut temp_curs)
    }

    /// Read the given data type `T` from `L` bytes on the wire without
    /// advancing the index of the reader.
    pub fn peek_part<T, const L: usize>(&mut self) -> Result<T, WireError>
    where
        T: WireReadPart,
    {
        let mut temp_curs = self.curs;
        T::read_wire_part::<L, E>(&mut temp_curs)
    }

    /// Read the given data type `T` from `size` bytes on the wire without
    /// advancing the index of the reader.
    pub fn peek_ref<T>(&mut self, size: usize) -> Result<&'a T, WireError>
    where
        T: WireReadRef + ?Sized,
    {
        let mut temp_curs = self.curs;
        T::read_wire_ref(&mut temp_curs, size)
    }

    /// Read the given data type `T` from the wire.
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

    /// Read the given data type `T` from the wire.
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

    /// Read the given data type `T` from `size`
    /// bytes on the wire.
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

    /// Read the given data type `T` from the wire.
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

    /// Read the given data type `T` from the
    /// remaining data on the wire. Note that this operation may succeed even
    /// if there are no bytes remaining on the wire for the given reader.
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

/// A wrapper around a slice of `&[u8]` slices that provides an easy interface for
/// reading data types from the vectored slices.
#[derive(Clone, Copy)]
pub struct VectoredReader<'a, const E: bool = true> {
    curs: VectoredCursor<'a>,
    initial_slice_cnt: usize,
}

impl<'a, const E: bool> VectoredReader<'a, E> {
    /// Create a `VectoredReader` that can read data types sequentially from the vectored
    /// slices `bytes`.
    pub fn new(bytes: VectoredBuf<'a>) -> Self {
        VectoredReader {
            curs: VectoredCursor::new(bytes),
            initial_slice_cnt: bytes.len(),
        }
    }

    /// Advance the reader's index forward by the given amount of bytes, returning an error if there
    /// are insufficient bytes on the wire to do so.
    pub fn advance(&mut self, amount: usize) -> Result<(), WireError> {
        let mut temp_curs = self.curs;
        let res = temp_curs.advance(amount);
        if res.is_ok() {
            self.curs = temp_curs;
        }
        res
    }

    /// Advance the reader's index forward by the given number of bytes, or to the end of the wire if the amount
    /// exceeds the number of remaining bytes.
    pub fn advance_up_to(&mut self, index: usize) {
        self.curs.advance_up_to(index);
    }

    /// Check if the reader has no more bytes left on the vectored wire that can be read. If any
    /// bytes remain, return [`WireError::ExtraBytes`]; otherwise, return Ok().
    pub fn finalize(&self) -> Result<(), WireError> {
        if self.is_empty() {
            Ok(())
        } else {
            Err(WireError::ExtraBytes)
        }
    }

    /// Check if the reader has no more bytes left on the vectored wire that can be read after
    /// the given action. If any bytes remain, return [`WireError::ExtraBytes`]; otherwise, return Ok().
    pub fn finalize_after<T>(action: Result<T, WireError>, reader: &Self) -> Result<T, WireError> {
        if action.is_ok() {
            reader.finalize()?;
        }
        action
    }

    /// Check whether the reader has any remaining bytes to be read.
    pub fn is_empty(&self) -> bool {
        self.curs.is_empty()
    }

    /// Read the given data type `T` from the vectored wire without advancing the
    /// index of the reader.
    pub fn peek<T>(&self) -> Result<T, WireError>
    where
        T: VectoredRead,
    {
        let mut temp_curs = self.curs; // Cheap and easy to just copy cursor and discard
        T::read_vectored::<E>(&mut temp_curs)
    }

    /// Read the given data type `T` from the vectored wire without advancing the
    /// index of the reader.
    pub fn peek_comp<T>(&mut self) -> Result<T, WireError>
    where
        T: VectoredReadComp<'a>,
    {
        let mut temp_curs = self.curs;
        T::read_vectored_comp::<E>(&mut temp_curs)
    }

    /// Read the given data type `T` from `L` bytes on the vectored wire without
    /// advancing the index of the reader.
    pub fn peek_part<T, const L: usize>(&mut self) -> Result<T, WireError>
    where
        T: VectoredReadPart,
    {
        let mut temp_curs = self.curs;
        T::read_vectored_part::<L, E>(&mut temp_curs)
    }

    /// Read the given data type `T` from `size` bytes on the vectored wire without
    /// advancing the index of the reader.
    pub fn peek_ref<T>(&self, size: usize) -> Result<&'a T, WireError>
    where
        T: VectoredReadRef + ?Sized,
    {
        let mut temp_curs = self.curs;
        T::read_vectored_ref(&mut temp_curs, size)
    }

    /// Read the given data type `T` from the vectored wire.
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

    /// Read the given data type `T` from the vectored wire.
    pub fn read_comp<T>(&mut self) -> Result<T, WireError>
    where
        T: VectoredReadComp<'a>,
    {
        let mut temp_curs = self.curs;
        let res = T::read_vectored_comp::<E>(&mut temp_curs);
        if res.is_ok() {
            self.curs = temp_curs;
        }
        res
    }

    /// Read the given data type `T` from `size` bytes on the
    /// vectored wire.
    pub fn red_part<T, const L: usize>(&mut self) -> Result<T, WireError>
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

    /// Read the given data type `T` from the vectored wire.
    pub fn read_ref<T>(&mut self, size: usize) -> Result<&'a T, WireError>
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

    /// Read the given data type `T` from the remaining data on the vectored wire.
    /// Note that this operation may succeed even if there are no bytes remaining
    /// on the vectored wire for the given reader.
    pub fn read_remaining<T>(&mut self) -> Result<&'a T, WireError>
    where
        T: VectoredReadRef + ?Sized,
    {
        self.read_ref(self.curs.remaining())
    }
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
                assert!(L > 0 && L < mem::size_of::<$int>()); // TODO: once more powerful const generic expressions are in rust, use them
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
                assert!(L > 0 && L < mem::size_of::<$int>()); // TODO: once more powerful const generic expressions are in rust, use them
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
