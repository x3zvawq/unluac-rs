//! 在 HIR proto 恢复失败时撤销预留的 composite artifact，并重映射稳定引用。
//!
//! 消费已构造的 HIR artifact，保持 arena 引用一致性；错误恢复策略由调用方决定。

use crate::hir::HirLowerError;
use crate::hir::common::{HirExpr, HirProtoRef};
use crate::hir::simplify::walk::{HirRewritePass, rewrite_proto};

use super::lower::{LowerArtifacts, LoweredProtoResult};

pub(super) fn discard_composite_factory_protos(
    composite_protos: &mut Vec<HirProtoRef>,
    child_results: &mut [LoweredProtoResult],
    artifacts: &mut LowerArtifacts,
) -> Result<(), HirLowerError> {
    let Some(first) = composite_protos.first().copied() else {
        return Ok(());
    };
    let start = first.index();
    let count = composite_protos.len();
    artifacts.protos.drain(start..start + count);
    artifacts.promotion_facts.drain(start..start + count);
    let remap = ProtoRefRemap { start, count };
    remap_artifact_proto_refs(artifacts, remap)?;
    remap_lowered_results(child_results, remap)?;
    composite_protos.clear();
    Ok(())
}

#[derive(Clone, Copy)]
struct ProtoRefRemap {
    start: usize,
    count: usize,
}

impl ProtoRefRemap {
    fn apply(self, proto: HirProtoRef) -> Option<HirProtoRef> {
        let index = proto.index();
        if index >= self.start + self.count {
            Some(HirProtoRef(index - self.count))
        } else if index < self.start {
            Some(proto)
        } else {
            None
        }
    }
}

struct ProtoRefRewrite {
    remap: ProtoRefRemap,
    removed_reference: Option<HirProtoRef>,
}

impl ProtoRefRewrite {
    fn rewrite_operation_sources(
        &mut self,
        sources: &mut crate::hir::common::HirOperationSources,
    ) -> bool {
        sources.rewrite_sites(|site| {
            if let Some(proto) = self.remap.apply(site.proto) {
                site.proto = proto;
            } else {
                self.removed_reference = Some(site.proto);
            }
        })
    }

    fn rewrite_source_site(
        &mut self,
        site: &mut Option<crate::hir::common::HirSourceSite>,
    ) -> bool {
        let Some(site) = site else {
            return false;
        };
        let Some(proto) = self.remap.apply(site.proto) else {
            self.removed_reference = Some(site.proto);
            return false;
        };
        site.proto = proto;
        true
    }
}

impl HirRewritePass for ProtoRefRewrite {
    fn rewrite_stmt(&mut self, stmt: &mut crate::hir::common::HirStmt) -> bool {
        match stmt {
            crate::hir::common::HirStmt::Return(ret) => {
                self.rewrite_source_site(&mut ret.frame_source)
            }
            crate::hir::common::HirStmt::TableSetList(batch) => {
                self.rewrite_source_site(&mut batch.source_site)
            }
            crate::hir::common::HirStmt::GenericFor(for_) => {
                self.rewrite_source_site(&mut for_.body_frame_source)
            }
            _ => false,
        }
    }

    fn rewrite_call(&mut self, call: &mut crate::hir::common::HirCallExpr) -> bool {
        self.rewrite_source_site(&mut call.source_site)
    }

    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        match expr {
            HirExpr::Unary(unary) => return self.rewrite_source_site(&mut unary.source_site),
            HirExpr::Binary(binary) => return self.rewrite_source_site(&mut binary.source_site),
            HirExpr::TableConstructor(table) => {
                let mut changed = self.rewrite_operation_sources(&mut table.sources);
                for field in &mut table.fields {
                    if let crate::hir::common::HirTableField::Record(record) = field {
                        changed |= self.rewrite_operation_sources(&mut record.write_sources);
                    }
                }
                return changed;
            }
            HirExpr::TableAccess(access) => {
                return self.rewrite_operation_sources(&mut access.sources);
            }
            HirExpr::GlobalRef(global) => {
                return self.rewrite_operation_sources(&mut global.sources);
            }
            _ => {}
        }
        let HirExpr::Closure(closure) = expr else {
            return false;
        };
        let Some(proto) = self.remap.apply(closure.proto) else {
            self.removed_reference = Some(closure.proto);
            return false;
        };
        closure.proto = proto;
        self.rewrite_source_site(&mut closure.source_site);
        true
    }

    fn rewrite_lvalue(&mut self, target: &mut crate::hir::common::HirLValue) -> bool {
        match target {
            crate::hir::common::HirLValue::Global(global) => {
                self.rewrite_operation_sources(&mut global.sources)
            }
            crate::hir::common::HirLValue::TableAccess(access) => {
                self.rewrite_operation_sources(&mut access.sources)
            }
            _ => false,
        }
    }
}

fn remap_artifact_proto_refs(
    artifacts: &mut LowerArtifacts,
    remap: ProtoRefRemap,
) -> Result<(), HirLowerError> {
    for (index, proto) in artifacts.protos.iter_mut().enumerate() {
        proto.id = HirProtoRef(index);
        artifacts.promotion_facts[index].relocate_proto_owner(proto.id);
        for child in &mut proto.children {
            *child = remap_proto_ref(*child, remap)?;
        }
        for (_, child) in &mut proto.detached_children {
            *child = remap_proto_ref(*child, remap)?;
        }
        let mut rewrite = ProtoRefRewrite {
            remap,
            removed_reference: None,
        };
        rewrite_proto(proto, &mut rewrite);
        if let Some(removed) = rewrite.removed_reference {
            return Err(removed_composite_reference_error(removed));
        }
    }
    Ok(())
}

fn remap_lowered_results(
    results: &mut [LoweredProtoResult],
    remap: ProtoRefRemap,
) -> Result<(), HirLowerError> {
    for result in results {
        result.id = remap_proto_ref(result.id, remap)?;
    }
    Ok(())
}

fn remap_proto_ref(proto: HirProtoRef, remap: ProtoRefRemap) -> Result<HirProtoRef, HirLowerError> {
    remap
        .apply(proto)
        .ok_or_else(|| removed_composite_reference_error(proto))
}

fn removed_composite_reference_error(proto: HirProtoRef) -> HirLowerError {
    HirLowerError::DiscardedCompositeStillReferenced {
        proto: proto.index(),
    }
}
