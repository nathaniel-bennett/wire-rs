# wire-rs

Extensible interface for converting data to/from wire protocol. Supports non-contiguous buffers (including &[IoSlice]) and is no_std compatible.

## Examples

To read data from a simple slice:

```rust
use wire_rs::{WireError, WireReader};

fn read_data<'a>(slice: &'a [u8]) -> Result<(u16, i8, &'a str), WireError> {
    let mut reader: WireReader = WireReader::new(slice);
    let s1 = reader.read()?;
    let s2 = reader.read()?;
    let s3 = reader.read_ref(7)?;
    Ok((s1, s2, s3))
}

```

To write data to a slice:

```rust
use wire_rs::{WireError, WireWriter};

fn write_data(slice: &mut [u8]) -> Result<(), WireError> {
    let mut writer: WireWriter = WireWriter::new(slice);
    writer.write(&10i32)?;
    writer.write_part::<u64, 3>(&0xFFu64)?; // Write the least significant 3 bytes of the given value to the wire (as long as the value will fit)
    writer.write("Hello, world!")?;
    writer.finalize()?; // Return an error if there were more bytes available on `slice` that we didn't write to
    Ok(())
}

```

To read/write data in little endian:

```rust
use wire_rs::{WireReader, WireWriter};

fn endianness() {
    let default_reader: WireReader = WireReader::new(&[]); 
    // ^ Big-endian by default (same for WireWriter)
    // Note: you may need to explicitly specify the `WireReader` type
    // such as in this case to use the default.

    let be_reader = WireReader::<true>::new(&[]);
    // Explicitly set to big-endian ^

    let le_writer = WireWriter::<false>::new(&mut []);
    // Explicitly set to little-endian ^
}

```

