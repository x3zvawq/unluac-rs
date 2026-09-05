//! 在最终 SSA 快照上冻结透明 Move 的语义值根。
//!
//! 输入是 compact/remap 后的 instruction use 与 Def 身份；例如 `r1 = r0; r2 = r1`
//! 的两个 Move 都指向 r0 的原值，遇到 Phi 则停止。它不证明物理 home 或快照可延后读取，
//! 也不解释 Structure 的 forwarded action。不可达 Move 缺少 use 时只让该查询失败，
//! 不能让未被任何消费者使用的指令阻止整个 proto 分析。

use super::super::common::InstrUseValues;
use super::*;

pub(super) fn freeze_move_values(
    proto: &LoweredProto,
    defs: &[Def],
    uses: &[InstrUseValues],
) -> Vec<Option<SsaValue>> {
    let mut resolved = vec![None; defs.len()];
    let mut state = vec![0u8; defs.len()];
    let mut path = Vec::new();
    for start in 0..defs.len() {
        if state[start] == 2 {
            continue;
        }
        let mut value = SsaValue::Def(DefId(start));
        let root = loop {
            let SsaValue::Def(def) = value else {
                break Some(value);
            };
            let Some(definition) = defs.get(def.index()).filter(|item| item.id == def) else {
                break None;
            };
            match state[def.index()] {
                2 => break resolved[def.index()],
                1 => break None,
                _ => {}
            }
            state[def.index()] = 1;
            path.push(def.index());
            let source = match proto.instrs.get(definition.instr.index()) {
                Some(LowInstr::Move(moved)) if moved.dst == definition.reg => uses
                    .get(definition.instr.index())
                    .and_then(|uses| uses.fixed.get(moved.src)),
                Some(_) => Some(value),
                None => None,
            };
            match source {
                Some(source) if source != value => value = source,
                root => break root,
            }
        };
        for index in path.drain(..) {
            resolved[index] = root;
            state[index] = 2;
        }
    }
    resolved
}
