//! 这个子模块负责从 HIR 闭包结构里提取 capture provenance。
//!
//! 它依赖 HIR 已经恢复好的 closure/capture 形状，只回答“子函数的 upvalue 来自哪里”，
//! 不会在这里分配最终名字。节点与 value pack 的遍历由共享 HIR visitor 提供，
//! 本层只消费 closure 回调，不另行展开 HIR 子节点或进入 child proto。
//! 例如：子闭包捕获某个 local 时，这里会记录它对应的捕获来源链。

use crate::hir::visit::{HirVisitor, visit_proto};
use crate::hir::{HirCapture, HirClosureExpr, HirExpr, HirModule, HirProtoRef};

use super::super::NamingError;
use super::super::common::{CapturedBinding, ClosureCaptureEvidence};

pub(super) fn build_capture_evidence(
    hir: &HirModule,
) -> Result<Vec<Option<ClosureCaptureEvidence>>, NamingError> {
    let mut evidence = vec![None; hir.protos.len()];
    for proto in &hir.protos {
        let mut collector = CaptureEvidenceCollector {
            function: proto.id,
            hir,
            evidence: &mut evidence,
            result: Ok(()),
        };
        visit_proto(proto, &mut collector);
        collector.result?;
    }
    Ok(evidence)
}

struct CaptureEvidenceCollector<'a> {
    function: HirProtoRef,
    hir: &'a HirModule,
    evidence: &'a mut [Option<ClosureCaptureEvidence>],
    result: Result<(), NamingError>,
}

impl HirVisitor for CaptureEvidenceCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if self.result.is_ok()
            && let HirExpr::Closure(closure) = expr
        {
            self.result =
                record_closure_capture_evidence(self.function, closure, self.hir, self.evidence);
        }
    }

    // closure 节点已经消费完整 capture 身份；命名证据不需要另行投影父级引用叶子。
    fn visit_capture(&mut self, _capture: &HirCapture) {}
}

fn record_closure_capture_evidence(
    parent: HirProtoRef,
    closure: &HirClosureExpr,
    hir: &HirModule,
    evidence: &mut [Option<ClosureCaptureEvidence>],
) -> Result<(), NamingError> {
    let child = hir
        .protos
        .get(closure.proto.index())
        .ok_or(NamingError::MissingFunction {
            function: closure.proto.index(),
        })?;
    if closure.captures.len() != child.upvalues.len() {
        return Err(NamingError::CaptureEvidenceMismatch {
            parent: parent.index(),
            child: closure.proto.index(),
            captures: closure.captures.len(),
            upvalues: child.upvalues.len(),
        });
    }

    let candidate = ClosureCaptureEvidence {
        parent,
        captures: closure
            .captures
            .iter()
            .map(|capture| CapturedBinding {
                parent,
                binding: capture.binding,
            })
            .collect(),
    };

    match &evidence[closure.proto.index()] {
        None => {
            evidence[closure.proto.index()] = Some(candidate);
            Ok(())
        }
        Some(existing) if *existing == candidate => Ok(()),
        Some(_) => Err(NamingError::ConflictingCaptureEvidence {
            child: closure.proto.index(),
        }),
    }
}
