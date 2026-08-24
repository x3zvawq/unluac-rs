//! 这个文件定义所有 bytecode family 共用的 Parser 资源边界。
//!
//! 原型树会被后续阶段递归遍历，因此必须在构造 raw tree 前统一限制深度；200 覆盖
//! pinned PUC-Lua/LuaJIT 编译器的边界，也为整个 Rust pipeline 留出稳定的系统栈余量。

use super::ParseError;

pub(crate) const MAX_PROTO_DEPTH: usize = 200;
/// Luau stores protos in a child-before-parent flat table.  Its postorder pipeline
/// is iterative, so the dialect can accept the depth emitted by the pinned compiler
/// while retaining a finite resource boundary for malformed blobs.
pub(crate) const MAX_LUAU_PROTO_DEPTH: usize = 4096;
/// Bound the number of lexical proto occurrences materialized from a shared flat
/// DAG.  A malformed diamond can otherwise expand exponentially even though its
/// serialized table is tiny; ordinary compiler output stays far below this cap.
pub(crate) const MAX_LUAU_PROTO_EXPANSION: usize = 65_536;

pub(crate) fn check_proto_depth(depth: usize) -> Result<(), ParseError> {
    if depth > MAX_PROTO_DEPTH {
        return Err(ParseError::DepthLimit {
            field: "proto",
            limit: MAX_PROTO_DEPTH,
            found: depth,
        });
    }
    Ok(())
}

pub(crate) fn check_luau_proto_depth(depth: usize) -> Result<(), ParseError> {
    if depth > MAX_LUAU_PROTO_DEPTH {
        return Err(ParseError::DepthLimit {
            field: "luau proto",
            limit: MAX_LUAU_PROTO_DEPTH,
            found: depth,
        });
    }
    Ok(())
}

pub(crate) fn check_luau_proto_expansion(expanded: usize) -> Result<(), ParseError> {
    if expanded > MAX_LUAU_PROTO_EXPANSION {
        return Err(ParseError::ExpansionLimit {
            field: "luau proto",
            limit: MAX_LUAU_PROTO_EXPANSION,
            found: expanded,
        });
    }
    Ok(())
}
