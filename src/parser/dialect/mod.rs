//! 这个目录存放各个 dialect 的 parser 实现。
//!
//! 公共 parser 层只保留统一入口和共享抽象；一旦进入这里，每个 dialect
//! 都可以自由定义自己的 opcode、operand 和 extra 结构，避免在公共层做
//! 过早统一。

pub mod lua51;
pub mod lua52;
pub mod lua53;
pub mod lua54;
pub mod lua55;
pub mod luajit;
pub mod luau;
pub mod puc_lua;
