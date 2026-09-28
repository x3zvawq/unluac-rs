//! 从最终 SSA 冻结透明 Move 的语义值根。
//!
//! 消费指令 use 和 Def 身份，不证明物理 home 或读取时点可移动。

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
