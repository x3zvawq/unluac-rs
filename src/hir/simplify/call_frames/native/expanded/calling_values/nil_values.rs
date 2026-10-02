//! 配对常量 nil guard 消去函数体后仍保留的参数 COPY 和 nil 返回。
//! 未读取 COPY、相邻结果定义及外层 CALL 的原参数身份共同约束候选。

use super::*;
use crate::transformer::InstrRef;

#[derive(Debug)]
pub(super) struct Candidate {
    pub source: crate::hir::HirSourceSite,
    pub source_pc: u32,
    pub end: InstrRef,
    pub value: LocalId,
    pub value_input: TempId,
    pub value_source: TempId,
    pub result: TempId,
    pub result_local: LocalId,
}

pub(super) fn candidates(proto: &HirProto, facts: &ProtoPromotionFacts) -> Vec<Candidate> {
    let mut copies = BTreeMap::new();
    for copy in facts.unread_copies() {
        if let Some(local) = facts.promoted_local_for_temp(copy.write.target) {
            copies
                .entry(local)
                .and_modify(|entry| *entry = None)
                .or_insert(Some(copy));
        }
    }
    let mut points = Vec::new();
    prefix::coordinates::visit(&proto.body, &mut 0, &mut |_, kind, stmt| {
        points.push((kind == PointKind::Statement).then_some(stmt));
    });
    points
        .windows(3)
        .chain(points.windows(4))
        .filter_map(|window| {
            let (copy, result, release, consumer) = match window {
                [Some(copy), Some(result), Some(consumer)] => (*copy, *result, None, *consumer),
                [
                    Some(copy),
                    Some(result),
                    Some(HirStmt::LocalRootRelease(release)),
                    Some(consumer),
                ] => (*copy, *result, Some(*release), *consumer),
                _ => return None,
            };
            if !pairs::scalar_write(copy) {
                return None;
            }
            let (value, HirExpr::LocalRef(input)) = scalar_local(copy)? else {
                return None;
            };
            if release.is_some_and(|released| released != value) {
                return None;
            }
            let (result_local, HirExpr::Nil) = scalar_local(result)? else {
                return None;
            };
            let call = match consumer {
                HirStmt::CallStmt(stmt) => &stmt.call,
                stmt => match scalar_local(stmt)?.1 {
                    HirExpr::Call(call) => call.as_ref(),
                    _ => return None,
                },
            };
            let copy = (*copies.get(&value)?)?;
            let source = crate::hir::HirSourceSite {
                proto: proto.id,
                instr: copy.instruction,
            };
            let nil_site = crate::hir::HirSourceSite {
                proto: proto.id,
                instr: InstrRef(source.instr.index() + 1),
            };
            let result_value = facts.operation_result_temp(nil_site)?;
            let home = facts.trusted_temp_home_slot(result_value)?;
            let frame = facts.native_call_frame(call)?;
            let index = call
                .args
                .fixed
                .iter()
                .position(|arg| *arg == HirExpr::LocalRef(result_local))?;
            // 候选拒绝[ProofIncomplete:CallFrame]：无读 COPY 只有连同相邻 nil 写和
            // 原 CALL 参数槽一起恢复，才不会吞掉独立声明或另一条返回准备。
            if !pairs::scalar_write(result)
                || call.args.tail.is_some()
                || call.source_site?.instr.index() != nil_site.instr.index() + 1
                || facts.call_argument_value(call, index) != Some(result_value)
                || facts.call_argument_preparation_instruction(call, index, &HirExpr::Nil)
                    != Some(nil_site.instr)
                || facts.promoted_local_for_temp(result_value) != Some(result_local)
                || facts.promoted_local_for_temp(copy.write.source?) != Some(*input)
                || copy.write.target_home.slot() != home.slot() + 1
                || copy.write.source_home.slot() >= home.slot()
                || frame.home.slot() >= home.slot()
            {
                return None;
            }
            Some(Candidate {
                source,
                source_pc: copy.after_pc,
                end: call.source_site?.instr,
                value,
                value_input: copy.write.target,
                value_source: copy.write.source?,
                result: result_value,
                result_local,
            })
        })
        .collect()
}
