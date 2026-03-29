use crate::parser::error::ParseError;
use crate::parser::raw::{
    RawDebugInfoCommon, RawLiteralConst, RawLocalVar, RawProto, RawString, RawUpvalueDescriptor,
};
use crate::parser::reader::BinaryReader;

/// 读取一个带显式计数前缀的序列。
pub(crate) fn collect_counted<T>(
    count: u32,
    mut parse_item: impl FnMut() -> Result<T, ParseError>,
) -> Result<Vec<T>, ParseError> {
    let mut items = Vec::with_capacity(count as usize);
    for _ in 0..count {
        items.push(parse_item()?);
    }
    Ok(items)
}

/// 把 `u32` 计数安全收窄成 `u8`，供 upvalue 这类协议字段复用。
pub(crate) fn count_u8(count: u32, field: &'static str) -> Result<u8, ParseError> {
    u8::try_from(count).map_err(|_| ParseError::IntegerOverflow {
        field,
        value: u64::from(count),
    })
}

/// 需要协议里显式存在字符串时，统一在这里把 `Option` 收紧成值。
pub(crate) fn require_present<T>(value: Option<T>, field: &'static str) -> Result<T, ParseError> {
    value.ok_or(ParseError::UnsupportedValue { field, value: 0 })
}

/// 校验逐 PC 行号数组长度是否和指令数一致。
pub(crate) fn validate_line_info_length(
    permissive: bool,
    line_count: usize,
    raw_instruction_words: usize,
) -> Result<(), ParseError> {
    if !permissive && line_count != 0 && line_count != raw_instruction_words {
        return Err(ParseError::UnsupportedValue {
            field: "line info length",
            value: line_count as u64,
        });
    }
    Ok(())
}

/// 校验“字段要么为 0，要么等于协议里另一份计数”的常见规则。
pub(crate) fn validate_optional_count_match(
    permissive: bool,
    field: &'static str,
    actual: u32,
    expected: u8,
) -> Result<(), ParseError> {
    if !permissive && actual != 0 && actual != u32::from(expected) {
        return Err(ParseError::UnsupportedValue {
            field,
            value: u64::from(actual),
        });
    }
    Ok(())
}

/// 统一读取 upvalue 描述符列表，具体扩展字段仍由版本层自己补。
pub(crate) fn parse_upvalue_descriptors(
    reader: &mut BinaryReader<'_>,
    count: u32,
) -> Result<Vec<RawUpvalueDescriptor>, ParseError> {
    collect_counted(count, || {
        Ok(RawUpvalueDescriptor {
            in_stack: reader.read_u8()? != 0,
            index: reader.read_u8()?,
        })
    })
}

/// 统一读取 Lua 5.4/5.5 风格的 upvalue 三元组：`in_stack / index / kind`。
pub(crate) fn parse_upvalues_with_kinds(
    reader: &mut BinaryReader<'_>,
    count: u32,
) -> Result<(Vec<RawUpvalueDescriptor>, Vec<u8>), ParseError> {
    let pairs = collect_counted(count, || {
        Ok((
            RawUpvalueDescriptor {
                in_stack: reader.read_u8()? != 0,
                index: reader.read_u8()?,
            },
            reader.read_u8()?,
        ))
    })?;
    Ok(pairs.into_iter().unzip())
}

/// 统一读取 local var 列表。
pub(crate) fn parse_local_vars(
    count: u32,
    parse_local_var: impl FnMut() -> Result<RawLocalVar, ParseError>,
) -> Result<Vec<RawLocalVar>, ParseError> {
    collect_counted(count, parse_local_var)
}

/// 统一读取可选的 upvalue 名字并丢弃 `None`。
pub(crate) fn parse_upvalue_names(
    count: u32,
    mut parse_name: impl FnMut() -> Result<Option<RawString>, ParseError>,
) -> Result<Vec<RawString>, ParseError> {
    let mut names = Vec::with_capacity(count as usize);
    for _ in 0..count {
        if let Some(name) = parse_name()? {
            names.push(name);
        }
    }
    Ok(names)
}

pub(crate) struct ClassicDebugSections {
    pub(crate) source: Option<RawString>,
    pub(crate) common: RawDebugInfoCommon,
}

pub(crate) trait ClassicDebugDriver<'a> {
    fn read_source(
        &mut self,
        reader: &mut BinaryReader<'a>,
    ) -> Result<Option<RawString>, ParseError>;
    fn read_count(
        &mut self,
        reader: &mut BinaryReader<'a>,
        field: &'static str,
    ) -> Result<u32, ParseError>;
    fn read_line(&mut self, reader: &mut BinaryReader<'a>) -> Result<u32, ParseError>;
    fn parse_local_var(&mut self, reader: &mut BinaryReader<'a>)
    -> Result<RawLocalVar, ParseError>;
    fn validate_upvalue_count(&mut self, count: u32) -> Result<(), ParseError>;
    fn parse_upvalue_name(
        &mut self,
        reader: &mut BinaryReader<'a>,
    ) -> Result<Option<RawString>, ParseError>;
}

/// 统一读取 Lua 5.2/5.3 风格的 classic debug body。
pub(crate) fn parse_classic_debug_sections<'a>(
    reader: &mut BinaryReader<'a>,
    raw_instruction_words: usize,
    permissive: bool,
    driver: &mut impl ClassicDebugDriver<'a>,
) -> Result<ClassicDebugSections, ParseError> {
    let source = driver.read_source(reader)?;

    let line_count = driver.read_count(reader, "line info count")?;
    let line_info = collect_counted(line_count, || driver.read_line(reader))?;
    validate_line_info_length(permissive, line_info.len(), raw_instruction_words)?;

    let local_count = driver.read_count(reader, "local var count")?;
    let local_vars = parse_local_vars(local_count, || driver.parse_local_var(reader))?;

    let upvalue_name_count = driver.read_count(reader, "upvalue name count")?;
    driver.validate_upvalue_count(upvalue_name_count)?;
    let upvalue_names =
        parse_upvalue_names(upvalue_name_count, || driver.parse_upvalue_name(reader))?;

    Ok(ClassicDebugSections {
        source,
        common: RawDebugInfoCommon {
            line_info,
            local_vars,
            upvalue_names,
        },
    })
}

/// 统一读取“计数 + tag + payload”风格的 literal 常量池。
pub(crate) fn parse_tagged_literal_pool<'a, ReadCount, ParseLiteral>(
    reader: &mut BinaryReader<'a>,
    mut read_count: ReadCount,
    mut parse_literal: ParseLiteral,
) -> Result<Vec<RawLiteralConst>, ParseError>
where
    ReadCount: for<'b> FnMut(&'b mut BinaryReader<'a>, &'static str) -> Result<u32, ParseError>,
    ParseLiteral:
        for<'b> FnMut(u8, usize, &'b mut BinaryReader<'a>) -> Result<RawLiteralConst, ParseError>,
{
    let count = read_count(reader, "constant count")?;
    collect_counted(count, || {
        let offset = reader.offset();
        let tag = reader.read_u8()?;
        parse_literal(tag, offset, reader)
    })
}

pub(crate) struct AbsLineInfoConfig {
    pub(crate) raw_instruction_words: usize,
    pub(crate) defined_start: u32,
    pub(crate) abslineinfo_marker: i8,
    pub(crate) permissive: bool,
}

pub(crate) struct AbsDebugSections {
    pub(crate) common: RawDebugInfoCommon,
    pub(crate) line_deltas: Vec<i8>,
    pub(crate) abs_line_pairs: Vec<(u32, u32)>,
}

pub(crate) trait AbsDebugDriver<'a> {
    fn read_count(
        &mut self,
        reader: &mut BinaryReader<'a>,
        field: &'static str,
    ) -> Result<u32, ParseError>;
    fn read_line_delta(&mut self, reader: &mut BinaryReader<'a>) -> Result<i8, ParseError>;
    fn prepare_abs_line_info(
        &mut self,
        reader: &mut BinaryReader<'a>,
        abs_line_count: u32,
    ) -> Result<(), ParseError>;
    fn read_abs_line_pair(
        &mut self,
        reader: &mut BinaryReader<'a>,
    ) -> Result<(u32, u32), ParseError>;
    fn parse_local_var(&mut self, reader: &mut BinaryReader<'a>)
    -> Result<RawLocalVar, ParseError>;
    fn validate_upvalue_count(&mut self, count: u32) -> Result<(), ParseError>;
    fn parse_upvalue_name(
        &mut self,
        reader: &mut BinaryReader<'a>,
    ) -> Result<Option<RawString>, ParseError>;
}

/// 统一读取 Lua 5.4/5.5 风格的 `lineinfo + abslineinfo + locals + upvalue names`。
pub(crate) fn parse_abs_debug_sections<'a>(
    reader: &mut BinaryReader<'a>,
    abs_line_info: AbsLineInfoConfig,
    driver: &mut impl AbsDebugDriver<'a>,
) -> Result<AbsDebugSections, ParseError> {
    let line_count = driver.read_count(reader, "line info count")?;
    let line_deltas = collect_counted(line_count, || driver.read_line_delta(reader))?;

    let abs_line_count = driver.read_count(reader, "abs line info count")?;
    driver.prepare_abs_line_info(reader, abs_line_count)?;
    let abs_line_pairs = collect_counted(abs_line_count, || driver.read_abs_line_pair(reader))?;

    validate_line_info_length(
        abs_line_info.permissive,
        line_deltas.len(),
        abs_line_info.raw_instruction_words,
    )?;
    let line_info = reconstruct_abs_line_info(
        abs_line_info.defined_start,
        &line_deltas,
        &abs_line_pairs,
        abs_line_info.abslineinfo_marker,
        abs_line_info.permissive,
        |(pc, _)| *pc,
        |(_, line)| *line,
    )?;

    let local_count = driver.read_count(reader, "local var count")?;
    let local_vars = parse_local_vars(local_count, || driver.parse_local_var(reader))?;

    let upvalue_name_count = driver.read_count(reader, "upvalue name count")?;
    driver.validate_upvalue_count(upvalue_name_count)?;
    let upvalue_names =
        parse_upvalue_names(upvalue_name_count, || driver.parse_upvalue_name(reader))?;

    Ok(AbsDebugSections {
        common: RawDebugInfoCommon {
            line_info,
            local_vars,
            upvalue_names,
        },
        line_deltas,
        abs_line_pairs,
    })
}

/// 统一读取 child proto 列表。
pub(crate) fn parse_child_protos(
    count: u32,
    parse_child: impl FnMut() -> Result<RawProto, ParseError>,
) -> Result<Vec<RawProto>, ParseError> {
    collect_counted(count, parse_child)
}

/// 把 Lua 5.4/5.5 的 `lineinfo + abslineinfo` 组合恢复成逐 PC 的源码行号。
pub(crate) fn reconstruct_abs_line_info<T>(
    defined_start: u32,
    line_deltas: &[i8],
    abs_line_info: &[T],
    abslineinfo_marker: i8,
    permissive: bool,
    abs_pc: impl Fn(&T) -> u32,
    abs_line: impl Fn(&T) -> u32,
) -> Result<Vec<u32>, ParseError> {
    if line_deltas.is_empty() {
        return Ok(Vec::new());
    }

    let mut lines = Vec::with_capacity(line_deltas.len());
    let mut current = i64::from(defined_start);
    let mut abs_index = 0usize;

    for (pc, delta) in line_deltas.iter().copied().enumerate() {
        if let Some(abs) = abs_line_info.get(abs_index)
            && abs_pc(abs) as usize == pc
        {
            current = i64::from(abs_line(abs));
            lines.push(abs_line(abs));
            abs_index += 1;
            continue;
        }

        if delta == abslineinfo_marker {
            if permissive {
                lines.push(current.max(0) as u32);
                continue;
            }
            return Err(ParseError::UnsupportedValue {
                field: "abs line info marker",
                value: pc as u64,
            });
        }

        current += i64::from(delta);
        if current < 0 {
            return Err(ParseError::NegativeValue {
                field: "line info",
                value: current,
            });
        }
        lines.push(
            u32::try_from(current).map_err(|_| ParseError::IntegerOverflow {
                field: "line info",
                value: current as u64,
            })?,
        );
    }

    Ok(lines)
}
