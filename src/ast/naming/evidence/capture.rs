//! 从 `AstModule::protos` 提取 Naming 所需的 capture provenance。

use crate::ast::AstModule;

use super::super::NamingError;
use super::super::common::ClosureCaptureEvidence;

pub(super) fn build_capture_evidence<'ast>(
    module: &'ast AstModule,
) -> Result<Vec<Option<ClosureCaptureEvidence<'ast>>>, NamingError> {
    let mut evidence = vec![None; module.protos.len()];
    for proto in &module.protos {
        let Some((parent, captures)) = &proto.parent_captures else {
            continue;
        };
        if module.protos.get(parent.index()).is_none() {
            return Err(NamingError::MissingFunction {
                function: parent.index(),
            });
        }
        if captures.len() != proto.upvalues.len() {
            return Err(NamingError::CaptureEvidenceMismatch {
                parent: parent.index(),
                child: proto.id.index(),
                captures: captures.len(),
                upvalues: proto.upvalues.len(),
            });
        }
        evidence[proto.id.index()] = Some(ClosureCaptureEvidence {
            parent: *parent,
            captures: captures.as_slice(),
        });
    }
    Ok(evidence)
}
