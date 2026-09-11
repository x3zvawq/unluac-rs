//! 将循环两臂持有的 canonical 输入槽位用于归属安装，不再从前驱和值重建身份。
//!
//! 例如同一前驱的两条平行边分别占槽位 1、2，生产者会把两槽都放入同一臂；
//! 此处逐槽标记，并保留双臂重叠供安装者按 header/result 合同报错。

use super::*;

pub(super) const LOOP_INSIDE: u8 = 1;
pub(super) const LOOP_OUTSIDE: u8 = 2;

pub(super) fn classify_loop_incomings(
    phi: &PhiCandidate,
    inside: &LoopValueArm,
    outside: &LoopValueArm,
) -> Result<Vec<u8>, StructureError> {
    let mut classes = vec![0; phi.incoming.len()];
    for (arm, bit) in [(inside, LOOP_INSIDE), (outside, LOOP_OUTSIDE)] {
        for slot in &arm.incoming_slots {
            let class = classes.get_mut(slot.index()).ok_or_else(|| {
                StructureError::invalid(format!(
                    "{} loop arm incoming #{} is outside its canonical phi",
                    phi.id,
                    slot.index()
                ))
            })?;
            *class |= bit;
        }
    }
    Ok(classes)
}
