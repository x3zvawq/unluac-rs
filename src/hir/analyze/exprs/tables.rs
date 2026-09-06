//! 统一 NewTable 的语句与单次表达式入口，保留分配方式和模板初始值。
//!
//! Transformer 已区分各 VM 的预分配与模板复制；这里仅把常量身份映射为 HIR
//! 字段，不再读取 raw opcode。模板中的 nil 数组槽与 hash 项也属于初始化事实，
//! 例如 TDUP {nil, nil, true} 不能变成空表后的一条 [3] 写入。
//! 同次降低同时发布原 hash 键身份；后续构造区域融合后，不能从 fields 猜哪些键属于模板。
//! 模板数组槽数包含索引 0，不能把只有零索引的模板和没有数组的模板合并为同一个容量。
//! Luau 的动态模板项以数值 0 预置；这里保留初值和原键，后续真实写入由构造区域消费。

use crate::hir::common::{
    HirExpr, HirRecordField, HirTableAllocation, HirTableConstructor, HirTableField,
};
use crate::transformer::{LoweredProto, NewTableInstr, TableAllocation};
use crate::value_semantics::table::TableExpression;

use super::expr_for_const;

pub(in crate::hir::analyze) fn expr_for_new_table(
    proto: &LoweredProto,
    instruction: &NewTableInstr,
) -> HirExpr {
    let mut table = HirTableConstructor::default();
    table.allocation = match &instruction.allocation {
        TableAllocation::Luau(allocation) => HirTableAllocation::Luau(*allocation),
        TableAllocation::LuauTemplate(entries) => {
            let mut hash_keys = Vec::with_capacity(entries.len());
            for (key, value) in entries {
                let key = expr_for_const(proto, *key);
                hash_keys.push(
                    key.table_key()
                        .expect("template key is a primitive constant"),
                );
                table.fields.push(HirTableField::Record(HirRecordField {
                    key,
                    value: value.map_or(HirExpr::Integer(0), |value| expr_for_const(proto, value)),
                }));
            }
            HirTableAllocation::LuauTemplate {
                hash_keys: hash_keys.into(),
            }
        }
        TableAllocation::PucBatched(allocation) => HirTableAllocation::PucBatched(*allocation),
        TableAllocation::Indexed {
            array_capacity,
            hash_bits,
        } => HirTableAllocation::Indexed {
            array_capacity: *array_capacity,
            hash_bits: *hash_bits,
        },
        TableAllocation::Template(template) => {
            for (index, constant) in template.array.iter().enumerate() {
                let value = expr_for_const(proto, *constant);
                if index == 0 {
                    if !matches!(value, HirExpr::Nil) {
                        table.fields.push(HirTableField::Record(HirRecordField {
                            key: HirExpr::Integer(0),
                            value,
                        }));
                    }
                } else {
                    table.fields.push(HirTableField::Array(value));
                }
            }
            let mut hash_keys = Vec::with_capacity(template.hash.len());
            for (key, value) in &template.hash {
                let key = expr_for_const(proto, *key);
                hash_keys.push(
                    key.table_key()
                        .expect("template hash key is a primitive constant"),
                );
                table.fields.push(HirTableField::Record(HirRecordField {
                    key,
                    value: expr_for_const(proto, *value),
                }));
            }
            HirTableAllocation::Template {
                array_slots: u32::try_from(template.array.len())
                    .expect("template array size fits u32"),
                hash_keys: hash_keys.into(),
            }
        }
    };
    HirExpr::TableConstructor(Box::new(table))
}
