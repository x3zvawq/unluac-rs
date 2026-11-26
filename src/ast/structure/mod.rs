//! 通用控制流结构化模块入口。

pub mod cond_fold;
pub mod reduce;
pub mod region;

pub use reduce::structure_proto;
pub use region::{CondExpr, Region, StateArm, StateTransition};
