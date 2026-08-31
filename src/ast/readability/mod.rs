//! AST readability：把前层已经合法的 AST 收敛成更接近源码的稳定形状。
//!
//! 这里不是给前层“补事实”或“兜底修结构”的阶段：
//! - 不负责替 AST build / HIR / Structure 补缺失语义
//! - 不负责把前层过度内联、过度结构化的问题继续静默修掉
//! - 只在前层事实已经足够稳定时，做源码可读性层面的保守整形

mod binding_flow;
mod binding_ref;
mod binding_tree;
mod branch_pretty;
mod cleanup;
mod control_flow;
mod expr_analysis;
mod field_access_sugar;
mod function_sugar;
mod global_decl_pretty;
mod goto_syntax_safety;
mod inline_exprs;
mod installer_iife;
mod literal_fold;
mod local_scope_limit;
mod materialize_temps;
mod statement_merge;
mod stmt_plan;
mod traverse;
mod visit;
mod walk;

use super::common::{AstModule, AstTargetDialect};
use crate::decompile::{DecompileContext, DecompileError, DecompileState};
use crate::scheduler::{
    InvalidationConvergence, InvalidationTag, PassDescriptor, PassPhase, run_invalidation_loop,
};
use crate::timing::TimingCollector;

/// 可调的源码形状阈值。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReadabilityOptions {
    pub return_inline_max_complexity: usize,
    pub index_inline_max_complexity: usize,
    pub args_inline_max_complexity: usize,
    pub access_base_inline_max_complexity: usize,
}

impl Default for ReadabilityOptions {
    fn default() -> Self {
        Self {
            return_inline_max_complexity: 10,
            index_inline_max_complexity: 10,
            args_inline_max_complexity: 6,
            access_base_inline_max_complexity: 5,
        }
    }
}

#[derive(Clone, Copy)]
pub(super) struct ReadabilityContext {
    pub target: AstTargetDialect,
    pub options: ReadabilityOptions,
}

/// AST 可读性变化的粗粒度标签。
///
/// 每个 pass 声明自己依赖和产出哪些标签，调度器根据 dirty set 决定哪些 pass 需要重跑。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum AstInvalidation {
    /// 语句相邻关系变化（影响 statement-merge, inline-exprs）。
    StatementAdjacency,
    /// 控制流形状变化（影响 branch-pretty 及其下游）。
    ControlFlowShape,
    /// 表达式形状变化（影响 field-access-sugar, inline-exprs）。
    ExprShape,
    /// 绑定关系变化（影响 function-sugar 等 binding 消费者）。
    BindingStructure,
    /// temp 存在性变化（影响 temp-materialize, inline-exprs）。
    TempPresence,
}

impl InvalidationTag for AstInvalidation {
    fn all() -> &'static [Self] {
        &[
            Self::StatementAdjacency,
            Self::ControlFlowShape,
            Self::ExprShape,
            Self::BindingStructure,
            Self::TempPresence,
        ]
    }
}

/// pass 的可执行入口，与 `PASS_DESCRIPTORS` 按下标一一对应。
struct ReadabilityPassEntry {
    apply: fn(&mut AstModule, ReadabilityContext) -> bool,
}

use AstInvalidation::*;

// Pass 描述符：声明每个 pass 依赖和产出哪些 invalidation tag。
//
// 排列顺序决定同一轮内的执行先后——把"生产者"放在"消费者"前面可以减少
// 不必要的多轮迭代。调度器会根据 dirty set 自动跳过不相关的 pass。
//
// Normal phase 处理主要形状收敛：
//   cleanup → statement-merge → branch-pretty → field-access-sugar → inline-exprs
//   → literal-fold
//
// Deferred phase 在 Normal 全部收敛后执行终态物化和语法糖：
//   temp-materialize → installer-iife → function-sugar → global-decl-pretty → goto-syntax-safety
//
// 如果 Deferred pass 产出新 invalidation，Normal phase 会重新收敛。
const PASS_DESCRIPTORS: &[PassDescriptor<AstInvalidation>] = &[
    // ── Normal phase ──
    PassDescriptor {
        name: "cleanup",
        phase: PassPhase::Normal,
        depends_on: &[
            StatementAdjacency,
            ControlFlowShape,
            ExprShape,
            BindingStructure,
            TempPresence,
        ],
        invalidates: &[StatementAdjacency, ExprShape, BindingStructure],
    },
    PassDescriptor {
        name: "statement-merge",
        phase: PassPhase::Normal,
        depends_on: &[StatementAdjacency, ControlFlowShape],
        invalidates: &[StatementAdjacency, ExprShape],
    },
    PassDescriptor {
        name: "branch-pretty",
        phase: PassPhase::Normal,
        // literal-fold can expose a constant condition after the initial branch pass;
        // rerun here so the control shell consumes that proven ExprShape fact.
        depends_on: &[ControlFlowShape, StatementAdjacency, ExprShape],
        invalidates: &[ControlFlowShape, StatementAdjacency],
    },
    PassDescriptor {
        name: "field-access-sugar",
        phase: PassPhase::Normal,
        depends_on: &[ExprShape],
        invalidates: &[ExprShape],
    },
    PassDescriptor {
        name: "inline-exprs",
        phase: PassPhase::Normal,
        depends_on: &[StatementAdjacency, ExprShape],
        invalidates: &[StatementAdjacency, ExprShape],
    },
    PassDescriptor {
        name: "literal-fold",
        phase: PassPhase::Normal,
        depends_on: &[ControlFlowShape, ExprShape],
        invalidates: &[ExprShape],
    },
    // ── Deferred phase ──
    PassDescriptor {
        name: "materialize-temps",
        phase: PassPhase::Deferred,
        depends_on: &[TempPresence],
        invalidates: &[TempPresence, BindingStructure, StatementAdjacency],
    },
    PassDescriptor {
        name: "installer-iife",
        phase: PassPhase::Deferred,
        depends_on: &[TempPresence, BindingStructure],
        invalidates: &[StatementAdjacency, ExprShape, BindingStructure],
    },
    PassDescriptor {
        name: "function-sugar",
        phase: PassPhase::Deferred,
        depends_on: &[TempPresence, BindingStructure, ExprShape],
        invalidates: &[StatementAdjacency, ExprShape],
    },
    PassDescriptor {
        name: "global-decl-pretty",
        phase: PassPhase::Deferred,
        depends_on: &[StatementAdjacency],
        invalidates: &[StatementAdjacency],
    },
    PassDescriptor {
        name: "goto-syntax-safety",
        phase: PassPhase::Deferred,
        depends_on: &[ControlFlowShape],
        invalidates: &[],
    },
    PassDescriptor {
        name: "local-scope-limit",
        phase: PassPhase::Deferred,
        depends_on: &[StatementAdjacency, BindingStructure],
        invalidates: &[],
    },
];

/// pass 执行入口，下标与 `PASS_DESCRIPTORS` 一一对应。
const PASS_ENTRIES: &[ReadabilityPassEntry] = &[
    ReadabilityPassEntry {
        apply: cleanup::apply,
    },
    ReadabilityPassEntry {
        apply: statement_merge::apply,
    },
    ReadabilityPassEntry {
        apply: branch_pretty::apply,
    },
    ReadabilityPassEntry {
        apply: field_access_sugar::apply,
    },
    ReadabilityPassEntry {
        apply: inline_exprs::apply,
    },
    ReadabilityPassEntry {
        apply: literal_fold::apply,
    },
    ReadabilityPassEntry {
        apply: materialize_temps::apply,
    },
    ReadabilityPassEntry {
        apply: installer_iife::apply,
    },
    ReadabilityPassEntry {
        apply: function_sugar::apply,
    },
    ReadabilityPassEntry {
        apply: global_decl_pretty::apply,
    },
    ReadabilityPassEntry {
        apply: goto_syntax_safety::apply,
    },
    ReadabilityPassEntry {
        apply: local_scope_limit::apply,
    },
];

const MAX_ROUNDS: usize = 64;

/// 对外的 readability 入口。
pub(crate) fn make_readable(
    state: &mut DecompileState,
    context: &DecompileContext<'_>,
) -> Result<(), DecompileError> {
    let ast = state.require_ast()?;
    state.readability = Some(make_readable_module(
        ast,
        context.requested_target,
        context.options.readability,
        context.timings,
        &context.options.debug.dump_passes,
    )?);
    Ok(())
}

/// 对已经合法的 AST 执行 readability pass 收敛。
pub(crate) fn make_readable_module(
    module: &AstModule,
    target: AstTargetDialect,
    options: ReadabilityOptions,
    timings: &TimingCollector,
    dump_passes: &[String],
) -> Result<AstModule, DecompileError> {
    let mut module = module.clone();
    let context = ReadabilityContext { target, options };

    let convergence = run_invalidation_loop(
        PASS_DESCRIPTORS,
        |index, name| {
            // 如果当前 pass 在 dump 列表中，先快照 before。关闭 debug feature 的构建
            // 不编译 AST renderer，因此这里会退化成 None。
            let before_snapshot = capture_ast_snapshot_if_requested(&module, dump_passes, name);

            let changed =
                timings.record(name, || (PASS_ENTRIES[index].apply)(&mut module, context));

            // pass 产生变化时输出 before/after diff
            if let Some(before) = before_snapshot.filter(|_| changed) {
                emit_ast_pass_diff_if_requested(name, before, &module);
            }

            changed
        },
        MAX_ROUNDS,
    );
    if let InvalidationConvergence::LimitExceeded { rounds } = convergence {
        return Err(DecompileError::PassLimitExceeded {
            stage: crate::decompile::DecompileStage::Ast,
            rounds,
        });
    }

    super::capture_scope::verify_forward_local_captures(&module)?;
    Ok(module)
}

#[cfg(feature = "decompile-debug")]
type AstPassSnapshot = String;

#[cfg(not(feature = "decompile-debug"))]
type AstPassSnapshot = ();

#[cfg(feature = "decompile-debug")]
fn capture_ast_snapshot_if_requested(
    module: &AstModule,
    dump_passes: &[String],
    pass_name: &str,
) -> Option<AstPassSnapshot> {
    dump_passes
        .iter()
        .any(|name| name == pass_name)
        .then(|| super::debug::dump_ast_snapshot(module))
}

#[cfg(not(feature = "decompile-debug"))]
fn capture_ast_snapshot_if_requested(
    _module: &AstModule,
    _dump_passes: &[String],
    _pass_name: &str,
) -> Option<AstPassSnapshot> {
    None
}

#[cfg(feature = "decompile-debug")]
fn emit_ast_pass_diff_if_requested(name: &str, before: AstPassSnapshot, module: &AstModule) {
    let after = super::debug::dump_ast_snapshot(module);
    eprintln!("=== [readability] pass={name} CHANGED ===");
    eprintln!("--- before ---");
    eprint!("{before}");
    eprintln!("--- after ---");
    eprint!("{after}");
    eprintln!("=== end ===");
}

#[cfg(not(feature = "decompile-debug"))]
fn emit_ast_pass_diff_if_requested(_name: &str, _before: AstPassSnapshot, _module: &AstModule) {}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;
    use crate::ast::common::{
        AstAssign, AstBlock, AstExpr, AstFunctionExpr, AstFunctionName, AstLValue, AstNameRef,
        AstStmt, AstSyntheticLocalId,
    };
    use crate::decompile::DecompileDialect;
    use crate::hir::{HirProtoRef, TempId};
    use crate::timing::TimingCollector;

    #[test]
    fn deferred_pipeline_materializes_temp_before_function_sugar() {
        let temp = TempId(7);
        let module = AstModule {
            entry_function: HirProtoRef(0),
            body: AstBlock {
                stmts: vec![AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::Name(AstNameRef::Temp(temp))],
                    values: vec![AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
                        function: HirProtoRef(1),
                        params: Vec::new(),
                        is_vararg: false,
                        named_vararg: None,
                        body: AstBlock::default(),
                        captured_bindings: BTreeSet::new(),
                        captured_params: BTreeSet::new(),
                    }))],
                }))],
            },
        };

        let readable = make_readable_module(
            &module,
            AstTargetDialect::new(DecompileDialect::Lua54),
            ReadabilityOptions::default(),
            &TimingCollector::new(false),
            &[],
        )
        .expect("readability should converge");

        let [AstStmt::FunctionDecl(decl)] = readable.body.stmts.as_slice() else {
            panic!("function sugar should consume the materialized assignment")
        };
        let AstFunctionName::Plain(path) = &decl.target else {
            panic!("direct assignment must remain a plain function")
        };
        assert_eq!(
            path.root,
            AstNameRef::SyntheticLocal(AstSyntheticLocalId(temp))
        );
    }
}
