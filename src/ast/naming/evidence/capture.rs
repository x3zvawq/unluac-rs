//! 从 HIR 闭包提取 Naming 所需的 capture provenance。
//!
//! 消费共享 visitor 与显式 capture，发布父子绑定来源，不分配最终名字。

use crate::hir::visit::{HirVisitor, visit_proto};
use crate::hir::{HirCapture, HirClosureExpr, HirModule, HirProtoRef};

use super::super::NamingError;
use super::super::common::ClosureCaptureEvidence;

pub(super) fn build_capture_evidence<'hir>(
    hir: &'hir HirModule,
) -> Result<Vec<Option<ClosureCaptureEvidence<'hir>>>, NamingError> {
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

struct CaptureEvidenceCollector<'hir, 'out> {
    function: HirProtoRef,
    hir: &'hir HirModule,
    evidence: &'out mut [Option<ClosureCaptureEvidence<'hir>>],
    result: Result<(), NamingError>,
}

impl<'hir> HirVisitor<'hir> for CaptureEvidenceCollector<'hir, '_> {
    fn visit_closure(&mut self, closure: &'hir HirClosureExpr) {
        if self.result.is_ok() {
            self.result =
                record_closure_capture_evidence(self.function, closure, self.hir, self.evidence);
        }
    }

    // closure 节点已经消费完整 capture 身份；命名证据不需要另行投影父级引用叶子。
    fn visit_capture(&mut self, _capture: &HirCapture) {}
}

fn record_closure_capture_evidence<'hir>(
    parent: HirProtoRef,
    closure: &'hir HirClosureExpr,
    hir: &'hir HirModule,
    evidence: &mut [Option<ClosureCaptureEvidence<'hir>>],
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
        captures: &closure.captures,
    };

    match &evidence[closure.proto.index()] {
        None => {
            evidence[closure.proto.index()] = Some(candidate);
            Ok(())
        }
        Some(existing)
            if existing.parent == candidate.parent
                && existing
                    .captures
                    .iter()
                    .map(|capture| capture.binding)
                    .eq(candidate.captures.iter().map(|capture| capture.binding)) =>
        {
            Ok(())
        }
        Some(_) => Err(NamingError::ConflictingCaptureEvidence {
            child: closure.proto.index(),
        }),
    }
}
