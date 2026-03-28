//! 这个文件提供 parser 层共享的底层二进制读取器。
//!
//! 它只负责“怎样按字节读取”，不负责“某个 dialect 怎样解释这些字节”，
//! 这样可以把二进制布局细节和语义解析规则拆开。

use super::error::ParseError;
use super::raw::Endianness;

pub(crate) struct BinaryReader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> BinaryReader<'a> {
    pub(crate) const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    pub(crate) const fn offset(&self) -> usize {
        self.offset
    }

    pub(crate) const fn remaining(&self) -> usize {
        self.bytes.len().saturating_sub(self.offset)
    }

    pub(crate) fn read_exact(&mut self, size: usize) -> Result<&'a [u8], ParseError> {
        if self.remaining() < size {
            return Err(ParseError::UnexpectedEof {
                offset: self.offset,
                requested: size,
                remaining: self.remaining(),
            });
        }

        let start = self.offset;
        self.offset += size;
        Ok(&self.bytes[start..self.offset])
    }

    pub(crate) fn read_u8(&mut self) -> Result<u8, ParseError> {
        Ok(self.read_exact(1)?[0])
    }

    pub(crate) fn read_array<const N: usize>(&mut self) -> Result<[u8; N], ParseError> {
        let bytes = self.read_exact(N)?;
        let mut array = [0_u8; N];
        array.copy_from_slice(bytes);
        Ok(array)
    }

    pub(crate) fn read_u64_sized(
        &mut self,
        size: u8,
        endianness: Endianness,
        field: &'static str,
    ) -> Result<u64, ParseError> {
        let size = usize::from(size);
        if !(1..=8).contains(&size) {
            return Err(ParseError::UnsupportedSize {
                field,
                value: size as u8,
            });
        }

        let bytes = self.read_exact(size)?;
        let mut buffer = [0_u8; 8];

        match endianness {
            Endianness::Little => buffer[..size].copy_from_slice(bytes),
            Endianness::Big => buffer[8 - size..].copy_from_slice(bytes),
        }

        Ok(match endianness {
            Endianness::Little => u64::from_le_bytes(buffer),
            Endianness::Big => u64::from_be_bytes(buffer),
        })
    }

    pub(crate) fn read_i64_sized(
        &mut self,
        size: u8,
        endianness: Endianness,
        field: &'static str,
    ) -> Result<i64, ParseError> {
        let value = self.read_u64_sized(size, endianness, field)?;
        let bits = u32::from(size) * 8;
        if bits == 64 {
            return Ok(match endianness {
                Endianness::Little => i64::from_le_bytes(value.to_le_bytes()),
                Endianness::Big => i64::from_be_bytes(value.to_be_bytes()),
            });
        }

        let shift = 64 - bits;
        Ok(((value << shift) as i64) >> shift)
    }

    pub(crate) fn read_f64_sized(
        &mut self,
        size: u8,
        endianness: Endianness,
    ) -> Result<f64, ParseError> {
        match size {
            4 => {
                let mut buffer = [0_u8; 4];
                buffer.copy_from_slice(self.read_exact(4)?);
                Ok(match endianness {
                    Endianness::Little => f32::from_le_bytes(buffer),
                    Endianness::Big => f32::from_be_bytes(buffer),
                } as f64)
            }
            8 => {
                let mut buffer = [0_u8; 8];
                buffer.copy_from_slice(self.read_exact(8)?);
                Ok(match endianness {
                    Endianness::Little => f64::from_le_bytes(buffer),
                    Endianness::Big => f64::from_be_bytes(buffer),
                })
            }
            value => Err(ParseError::UnsupportedSize {
                field: "number_size",
                value,
            }),
        }
    }

    pub(crate) fn read_varint_u64_lua54(
        &mut self,
        limit: u64,
        field: &'static str,
    ) -> Result<u64, ParseError> {
        let mut value = 0_u64;
        let shifted_limit = limit >> 7;

        loop {
            let byte = self.read_u8()?;
            if value >= shifted_limit {
                return Err(ParseError::IntegerOverflow { field, value });
            }
            value = (value << 7) | u64::from(byte & 0x7f);
            if (byte & 0x80) != 0 {
                return Ok(value);
            }
        }
    }

    pub(crate) fn read_varint_u64_lua55(
        &mut self,
        limit: u64,
        field: &'static str,
    ) -> Result<u64, ParseError> {
        let mut value = 0_u64;
        let shifted_limit = limit >> 7;

        loop {
            let byte = self.read_u8()?;
            if value > shifted_limit {
                return Err(ParseError::IntegerOverflow { field, value });
            }
            value = (value << 7) | u64::from(byte & 0x7f);
            if (byte & 0x80) == 0 {
                return Ok(value);
            }
        }
    }

    pub(crate) fn read_uleb128_u32(&mut self, field: &'static str) -> Result<u32, ParseError> {
        let mut value = 0_u32;
        let mut shift = 0_u32;

        loop {
            let byte = self.read_u8()?;
            let payload = u32::from(byte & 0x7f);
            if shift >= 32 || (payload << shift) >> shift != payload {
                return Err(ParseError::IntegerOverflow {
                    field,
                    value: u64::from(value),
                });
            }
            value |= payload << shift;
            if (byte & 0x80) == 0 {
                return Ok(value);
            }
            shift += 7;
            if shift >= 32 {
                return Err(ParseError::IntegerOverflow {
                    field,
                    value: u64::from(value),
                });
            }
        }
    }

    pub(crate) fn read_uleb128_33(
        &mut self,
        field: &'static str,
    ) -> Result<(u32, bool), ParseError> {
        let first = self.read_u8()?;
        let is_wide = (first & 1) != 0;
        let mut value = u32::from(first >> 1);

        if value < 0x40 {
            return Ok((value, is_wide));
        }

        value &= 0x3f;
        let mut shift = 6_u32;
        loop {
            let byte = self.read_u8()?;
            let payload = u32::from(byte & 0x7f);
            if shift >= 32 || (payload << shift) >> shift != payload {
                return Err(ParseError::IntegerOverflow {
                    field,
                    value: u64::from(value),
                });
            }
            value |= payload << shift;
            if (byte & 0x80) == 0 {
                return Ok((value, is_wide));
            }
            shift += 7;
            if shift >= 32 {
                return Err(ParseError::IntegerOverflow {
                    field,
                    value: u64::from(value),
                });
            }
        }
    }
}
