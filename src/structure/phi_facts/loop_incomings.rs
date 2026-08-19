//! 分类循环 inside/outside incoming 与 canonical carried 值；依赖 loop value arms 和 SSA，不负责安装最终计划；例如核对同一 header phi 的两臂身份。

use super::*;

pub(super) const LOOP_INSIDE: u8 = 1;
pub(super) const LOOP_OUTSIDE: u8 = 2;

/// 把 loop arm evidence 一次投影到 canonical incoming ordinal。
///
/// 同一 predecessor 的平行 CFG edge 读取相同 block-exit SSA 值，因此用稠密 block
/// 下标标记 arm membership；epoch 避免为每个 phi 清空整张 block arena。
pub(super) struct LoopIncomingClassifier {
    epoch: usize,
    pred_epochs: Vec<usize>,
    pred_values: Vec<SsaValue>,
    pred_classes: Vec<u8>,
    synthetic_epoch: usize,
    synthetic_value: SsaValue,
    synthetic_class: u8,
}

impl LoopIncomingClassifier {
    pub(super) fn new(dataflow: &DataflowFacts) -> Result<Self, StructureError> {
        let max_pred = dataflow
            .phi_candidates
            .iter()
            .flat_map(|phi| phi.incoming.iter().filter_map(|incoming| incoming.pred))
            .map(BlockRef::index)
            .max();
        let len = max_pred
            .map(|pred| {
                pred.checked_add(1).ok_or_else(|| {
                    StructureError::invalid("phi predecessor index overflows its dense arena")
                })
            })
            .transpose()?
            .unwrap_or(0);
        let mut pred_epochs = Vec::new();
        pred_epochs
            .try_reserve_exact(len)
            .map_err(|_| StructureError::invalid("phi predecessor arena is too large"))?;
        pred_epochs.resize(len, 0);
        Ok(Self {
            epoch: 0,
            pred_epochs,
            pred_values: vec![SsaValue::Entry(Reg(0)); len],
            pred_classes: vec![0; len],
            synthetic_epoch: 0,
            synthetic_value: SsaValue::Entry(Reg(0)),
            synthetic_class: 0,
        })
    }

    pub(super) fn classify(
        &mut self,
        phi: &PhiCandidate,
        inside: &LoopValueArm,
        outside: &LoopValueArm,
    ) -> Result<Vec<u8>, StructureError> {
        self.epoch = self
            .epoch
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("loop incoming classifier epoch overflow"))?;
        for incoming in &phi.incoming {
            self.record_canonical(phi.id, incoming.pred, incoming.value)?;
        }
        self.mark_arm(phi.id, inside, LOOP_INSIDE)?;
        self.mark_arm(phi.id, outside, LOOP_OUTSIDE)?;
        phi.incoming
            .iter()
            .map(|incoming| self.class_for(phi.id, incoming.pred, incoming.value))
            .collect()
    }

    pub(super) fn record_canonical(
        &mut self,
        phi: PhiId,
        pred: Option<BlockRef>,
        value: SsaValue,
    ) -> Result<(), StructureError> {
        let (epoch, stored, class) = match pred {
            Some(pred) => {
                let index = pred.index();
                let Some(epoch) = self.pred_epochs.get_mut(index) else {
                    return Err(StructureError::invalid(format!(
                        "{phi} predecessor {pred} is outside the dense block arena"
                    )));
                };
                (
                    epoch,
                    &mut self.pred_values[index],
                    &mut self.pred_classes[index],
                )
            }
            None => (
                &mut self.synthetic_epoch,
                &mut self.synthetic_value,
                &mut self.synthetic_class,
            ),
        };
        if *epoch == self.epoch {
            if *stored != value {
                return Err(StructureError::invalid(format!(
                    "{phi} has inconsistent SSA values from one predecessor"
                )));
            }
        } else {
            *epoch = self.epoch;
            *stored = value;
            *class = 0;
        }
        Ok(())
    }

    pub(super) fn mark_arm(
        &mut self,
        phi: PhiId,
        arm: &LoopValueArm,
        bit: u8,
    ) -> Result<(), StructureError> {
        for incoming in &arm.incomings {
            let (epoch, stored, class) = match incoming.pred {
                Some(pred) => {
                    let index = pred.index();
                    let Some(epoch) = self.pred_epochs.get(index) else {
                        return Err(StructureError::invalid(format!(
                            "{phi} loop arm predecessor {pred} is outside the dense block arena"
                        )));
                    };
                    (
                        epoch,
                        &self.pred_values[index],
                        &mut self.pred_classes[index],
                    )
                }
                None => (
                    &self.synthetic_epoch,
                    &self.synthetic_value,
                    &mut self.synthetic_class,
                ),
            };
            if *epoch != self.epoch || *stored != incoming.value {
                return Err(StructureError::invalid(format!(
                    "{phi} loop arm contains a non-canonical incoming"
                )));
            }
            *class |= bit;
        }
        Ok(())
    }

    pub(super) fn class_for(
        &self,
        phi: PhiId,
        pred: Option<BlockRef>,
        value: SsaValue,
    ) -> Result<u8, StructureError> {
        let (epoch, stored, class) = match pred {
            Some(pred) => {
                let index = pred.index();
                let Some(epoch) = self.pred_epochs.get(index) else {
                    return Err(StructureError::invalid(format!(
                        "{phi} predecessor {pred} is outside the dense block arena"
                    )));
                };
                (epoch, &self.pred_values[index], self.pred_classes[index])
            }
            None => (
                &self.synthetic_epoch,
                &self.synthetic_value,
                self.synthetic_class,
            ),
        };
        if *epoch != self.epoch || *stored != value {
            return Err(StructureError::invalid(format!(
                "{phi} canonical incoming changed during loop classification"
            )));
        }
        Ok(class)
    }
}
