//! 这个模块归档共享分析层的 unit 风格测试。
//!
//! 这里优先使用手工构造的 low-IR 夹具，目的是直接固定 CFG / GraphFacts /
//! Dataflow 的共享语义，而不是把断言间接绑死到某个 dialect 的 parser 上。

mod cfg_dataflow;
mod generate;
mod hir;
mod structure;
