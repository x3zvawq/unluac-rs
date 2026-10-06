//! 将 NewTable 的分配方式、常量模板和 source site 降低为 HIR 构造器事实。
//!
//! 消费 Transformer 的初始化协议，为后续构造区域提供字段与原键身份。

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
            // nil 槽也属于原模板容量；省略它们会把 TDUP 初始化变成运行时稀疏写入。
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

/// 被冻结的条件/值区域不再单独发射内部字段写；按 Dataflow 的私有初始化组
/// 完整降低它们，不能只返回 NEWTABLE 的空 seed。组内原容量和单类写序已验证。
pub(super) fn expr_for_private_initialization(
    lowering: &super::ProtoLowering<'_>,
    allocation: crate::structure::DefId,
    instruction: &NewTableInstr,
) -> HirExpr {
    use crate::hir::common::{HirOperationSources, HirSourceSite};
    use crate::transformer::{AccessKey, LowInstr};
    let source = HirSourceSite {
        proto: lowering.id,
        instr: lowering.dataflow.def_instr(allocation),
    };
    let HirExpr::TableConstructor(mut table) =
        expr_for_new_table(lowering.proto, instruction, source)
    else {
        unreachable!("NEWTABLE lowers to a constructor");
    };
    for &instr in lowering.dataflow.table_initialization_writes(allocation) {
        let block = lowering.dataflow.def_block(allocation);
        match &lowering.proto.instrs[instr.index()] {
            LowInstr::SetTable(write)
                if matches!(instruction.allocation, TableAllocation::Indexed { .. }) =>
            {
                // Dataflow 已核对连续的 TSETI 数组位置；开放尾批次继续使用原 value pack。
                let value = super::expr_for_value_operand_single_eval_pure_operand(
                    lowering,
                    block,
                    instr,
                    write.value,
                );
                table.fields.push(HirTableField::Array(value));
            }
            LowInstr::SetTable(write) => {
                let key = match write.key {
                    AccessKey::Const(key) => expr_for_const(lowering.proto, key),
                    AccessKey::Integer(key) => HirExpr::Integer(key),
                    AccessKey::Reg(key) => super::expr_for_reg_use_single_eval_with_call_policy(
                        lowering, block, instr, key, true,
                    ),
                };
                let value = super::expr_for_value_operand_single_eval_pure_operand(
                    lowering,
                    block,
                    instr,
                    write.value,
                );
                table.fields.push(HirTableField::Record(HirRecordField {
                    write_sources: HirOperationSources::Single(HirSourceSite {
                        proto: lowering.id,
                        instr,
                    }),
                    key,
                    value,
                }));
            }
            LowInstr::SetList(write) => {
                let values =
                    super::lower_value_pack_single_eval(lowering, block, instr, write.values);
                table
                    .fields
                    .extend(values.fixed.into_iter().map(HirTableField::Array));
                table.trailing_multivalue = values.tail;
            }
            _ => unreachable!("private initialization has only field/list writes"),
        }
    }
    HirExpr::TableConstructor(table)
}
