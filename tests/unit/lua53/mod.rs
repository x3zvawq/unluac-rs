//! Lua 5.3 的层内契约测试入口。
//!
//! 这里先覆盖 parser/transformer 两层，重点锁住 5.3 的 header 差异、整数/浮点
//! 常量标签，以及新增的整除和位运算 lowering。

mod parser;
mod transformer;
