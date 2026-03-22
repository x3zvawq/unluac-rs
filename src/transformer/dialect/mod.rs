//! 这个目录存放各个 dialect 的 transformer 实现。
//!
//! low-IR 契约应该统一，但 lowering 规则天然依赖具体字节码语义；按 dialect
//! 拆目录，可以让每一套规则和它的调试视图挨在一起演进，不把公共层重新撑大。

pub mod lua51;
