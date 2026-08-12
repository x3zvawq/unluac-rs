//! 这个文件定义所有 bytecode family 共用的 Parser 资源边界。
//!
//! 原型树会被后续阶段递归遍历，因此必须在构造 raw tree 前统一限制深度；200 覆盖
//! pinned PUC-Lua/LuaJIT 编译器的边界，也为整个 Rust pipeline 留出稳定的系统栈余量。

use super::ParseError;

pub(crate) const MAX_PROTO_DEPTH: usize = 200;

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
