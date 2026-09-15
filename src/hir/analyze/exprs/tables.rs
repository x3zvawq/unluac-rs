//! 统一 NewTable 的语句与单次表达式入口，保留分配方式和模板初始值。
//!
//! Transformer 已区分各 VM 的预分配与模板复制；这里仅把常量身份映射为 HIR
//! 字段，不再读取 raw opcode。模板中的 nil 数组槽与 hash 项也属于初始化事实，
//! 例如 TDUP {nil, nil, true} 不能变成空表后的一条 [3] 写入。
//! 同次降低同时发布原 hash 键身份；后续构造区域融合后，不能从 fields 猜哪些键属于模板。
//! 分配保留原 source site，跨字段重建仍能查询该时点的 home 和开放引用状态。
//! 键成员索引在此建立并共享；JIT 原子模板的 hash 按稳定 key 身份发布，数组保持原顺序。
//! hash dump 次序受 VM 随机散列影响，不是字段求值顺序；后续运行时写入仍保持事件顺序。
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
    source_site: crate::hir::common::HirSourceSite,
) -> HirExpr {
    let mut table = HirTableConstructor::default();
    table.sources = crate::hir::common::HirOperationSources::Single(source_site);
    table.allocation = match &instruction.allocation {
        TableAllocation::Luau(allocation) => HirTableAllocation::Luau(*allocation),
        TableAllocation::LuauTemplate(entries) => {
            let mut hash_keys = std::collections::BTreeSet::new();
            for (key, value) in entries {
                let key = expr_for_const(proto, *key);
                hash_keys.insert(
                    key.table_key()
                        .expect("template key is a primitive constant"),
                );
                table.fields.push(HirTableField::Record(HirRecordField {
                    write_sources: crate::hir::common::HirOperationSources::Unknown,
                    key,
                    value: value.map_or(HirExpr::Integer(0), |value| expr_for_const(proto, value)),
                }));
            }
            // None 项是模板原子预置的零值，Some 项是真正模板常量；两者可交错。
            // 按位置发布一次性角色，后层不能把再次出现的数值 0 当成模板初值。
            table.implicit_template_fields.extend(
                entries
                    .iter()
                    .enumerate()
                    .filter_map(|(index, (_, value))| value.is_none().then_some(index)),
            );
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
                            write_sources: crate::hir::common::HirOperationSources::Unknown,
                            key: HirExpr::Integer(0),
                            value,
                        }));
                    }
                } else {
                    table.fields.push(HirTableField::Array(value));
                }
            }
            let mut hash_fields: Vec<_> = template
                .hash
                .iter()
                .map(|(key, value)| {
                    let key = expr_for_const(proto, *key);
                    let identity = key
                        .table_key()
                        .expect("template hash key is a primitive constant");
                    (identity, key, expr_for_const(proto, *value))
                })
                .collect();
            // TDUP 的常量 hash 项属于同一次分配，没有彼此间的求值事件。
            // 只在首次生成字段序列时消除随机 dump 次序，不能排序后续融合的真实写入。
            hash_fields.sort_by(|left, right| left.0.cmp(&right.0));
            let mut hash_keys = std::collections::BTreeSet::new();
            for (identity, key, value) in hash_fields {
                let implicit_nil = matches!(&value, HirExpr::Nil);
                hash_keys.insert(identity);
                let field_index = table.fields.len();
                table.fields.push(HirTableField::Record(HirRecordField {
                    write_sources: crate::hir::common::HirOperationSources::Unknown,
                    key,
                    value,
                }));
                if implicit_nil {
                    // TDUP hash 中的 nil marker 携带原模板 key；lowering 不从相邻指令
                    // 猜它是否会被覆盖，只有完整 constructor 事务看到同键后写时才消费。
                    table.implicit_template_fields.insert(field_index);
                }
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
