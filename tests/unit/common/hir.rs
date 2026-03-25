//! 这些测试固定 HIR 第一版初始恢复的共享契约。
//!
//! 当前 HIR 会经过“初始恢复 + simplify”两步，所以这里重点钉住：
//! 1. 线性 low-IR 是否成功提升成变量世界，并消掉明显机械的 temp 转发；
//! 2. 简单 branch 是否能稳定恢复成 `If`；
//! 3. 简单条件链短路是否能稳定恢复成 `LogicalAnd / LogicalOr`；
//! 4. 共享短路子图是否能在 HIR 中保留成 `Decision`，而不是树化成重复片段。
//! 5. reducible 且无 goto 的基础 loop 是否能稳定恢复成 `while / repeat / numeric for`。
//! 6. loop-local 的 continue-like requirement 是否能稳定恢复成 `Continue` 或更自然的 loop 控制。

use unluac::cfg::{analyze_dataflow, analyze_graph_facts, build_cfg_graph};
use unluac::decompile::DebugDetail;
use unluac::hir::{
    HirExpr, HirLValue, HirStmt, HirTableField, HirTableKey, LocalId, analyze_hir, dump_hir,
};
use unluac::parser::{
    ChunkHeader, Dialect, DialectConstPoolExtra, DialectDebugExtra, DialectHeaderExtra,
    DialectUpvalueExtra, DialectVersion, Endianness, Lua51ConstPoolExtra, Lua51DebugExtra,
    Lua51HeaderExtra, Lua51UpvalueExtra, Origin, ProtoFrameInfo, ProtoLineRange, ProtoSignature,
    RawConstPool, RawConstPoolCommon, RawDebugInfo, RawDebugInfoCommon, RawUpvalueInfo,
    RawUpvalueInfoCommon, Span,
};
use unluac::structure::analyze_structure;
use unluac::transformer::{
    AccessBase, AccessKey, BinaryOpInstr, BinaryOpKind, BranchCond, BranchInstr, BranchOperands,
    BranchPredicate, ConstRef, GenericForCallInstr, GenericForLoopInstr, InstrRef, JumpInstr,
    LoadBoolInstr, LoadConstInstr, LowInstr, LoweredChunk, LoweredProto, LoweringMap, MoveInstr,
    NumericForInitInstr, NumericForLoopInstr, Reg, RegRange, ResultPack, ReturnInstr, ValueOperand,
    ValuePack,
};

fn is_var_ref(expr: &HirExpr) -> bool {
    matches!(expr, HirExpr::TempRef(_) | HirExpr::LocalRef(_))
}

fn is_integer_init_stmt(stmt: &HirStmt, value: i64) -> bool {
    match stmt {
        HirStmt::Assign(assign) => matches!(
            assign.targets.as_slice(),
            [HirLValue::Temp(_)] if matches!(assign.values.as_slice(), [HirExpr::Integer(actual)] if *actual == value)
        ),
        HirStmt::LocalDecl(local_decl) => matches!(
            local_decl.bindings.as_slice(),
            [LocalId(_)] if matches!(local_decl.values.as_slice(), [HirExpr::Integer(actual)] if *actual == value)
        ),
        _ => false,
    }
}

fn find_table_constructor_in_stmt(stmt: &HirStmt) -> Option<&unluac::hir::HirTableConstructor> {
    match stmt {
        HirStmt::LocalDecl(local_decl) => local_decl.values.iter().find_map(|expr| match expr {
            HirExpr::TableConstructor(table) => Some(table.as_ref()),
            _ => None,
        }),
        HirStmt::Assign(assign) => assign.values.iter().find_map(|expr| match expr {
            HirExpr::TableConstructor(table) => Some(table.as_ref()),
            _ => None,
        }),
        HirStmt::Return(ret) => ret.values.iter().find_map(|expr| match expr {
            HirExpr::TableConstructor(table) => Some(table.as_ref()),
            _ => None,
        }),
        _ => None,
    }
}

mod analyze_hir_shared {
    use super::*;

    #[test]
    fn lowers_linear_proto_into_temp_assignments_and_calls() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(0),
                value: ConstRef(0),
            }),
            LowInstr::GetTable(unluac::transformer::GetTableInstr {
                dst: Reg(1),
                base: AccessBase::Env,
                key: AccessKey::Const(ConstRef(1)),
            }),
            LowInstr::Move(MoveInstr {
                dst: Reg(2),
                src: Reg(0),
            }),
            LowInstr::Call(unluac::transformer::CallInstr {
                callee: Reg(1),
                args: ValuePack::Fixed(RegRange::new(Reg(2), 1)),
                results: unluac::transformer::ResultPack::Ignore,
                kind: unluac::transformer::CallKind::Normal,
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let proto = &hir.protos[0];

        assert_eq!(proto.temps.len(), 3);
        assert_eq!(proto.body.stmts.len(), 3);
        assert!(is_integer_init_stmt(&proto.body.stmts[0], 41));
        assert!(matches!(
            &proto.body.stmts[1],
            HirStmt::CallStmt(call_stmt)
                if matches!(&call_stmt.call.callee, HirExpr::GlobalRef(global) if global.name == "print")
                    && matches!(call_stmt.call.args.as_slice(), [arg] if is_var_ref(arg))
        ));
        assert!(matches!(
            &proto.body.stmts[2],
            HirStmt::Return(ret)
                if matches!(ret.values.as_slice(), [value] if is_var_ref(value))
        ));
    }

    #[test]
    fn lowers_open_value_pack_with_fixed_prefix() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(0),
                value: ConstRef(0),
            }),
            LowInstr::GetTable(unluac::transformer::GetTableInstr {
                dst: Reg(1),
                base: AccessBase::Env,
                key: AccessKey::Const(ConstRef(1)),
            }),
            LowInstr::Call(unluac::transformer::CallInstr {
                callee: Reg(1),
                args: ValuePack::Fixed(RegRange::new(Reg(2), 0)),
                results: unluac::transformer::ResultPack::Open(Reg(1)),
                kind: unluac::transformer::CallKind::Normal,
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Open(Reg(0)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let proto = &hir.protos[0];
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());

        assert!(
            matches!(
                proto.body.stmts.as_slice(),
                [HirStmt::Return(ret)]
                    if matches!(
                        ret.values.as_slice(),
                        [HirExpr::Integer(41), HirExpr::Call(call)]
                            if call.multiret
                                && call.args.is_empty()
                                && matches!(&call.callee, HirExpr::GlobalRef(global) if global.name == "print")
                    )
            ),
            "{dump}"
        );
        assert!(
            dump.contains("return 41, call(normal) global(print)()"),
            "{dump}"
        );
    }

    #[test]
    fn keeps_set_list_as_structured_hir_stmt_when_constructor_region_is_not_stable() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::NewTable(unluac::transformer::NewTableInstr { dst: Reg(0) }),
            LowInstr::GetTable(unluac::transformer::GetTableInstr {
                dst: Reg(1),
                base: AccessBase::Env,
                key: AccessKey::Const(ConstRef(1)),
            }),
            LowInstr::Call(unluac::transformer::CallInstr {
                callee: Reg(1),
                args: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
                results: ResultPack::Ignore,
                kind: unluac::transformer::CallKind::Normal,
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(2),
                value: ConstRef(2),
            }),
            LowInstr::SetList(unluac::transformer::SetListInstr {
                base: Reg(0),
                values: ValuePack::Fixed(RegRange::new(Reg(2), 1)),
                start_index: 1,
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let proto = &hir.protos[0];
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());

        assert!(
            proto.body.stmts.iter().any(|stmt| {
                matches!(
                    stmt,
                    HirStmt::TableSetList(set_list)
                        if set_list.start_index == 1
                            && matches!(&set_list.base, HirExpr::LocalRef(_) | HirExpr::TempRef(_))
                            && matches!(set_list.values.as_slice(), [HirExpr::Integer(0)])
                            && set_list.trailing_multivalue.is_none()
                )
            }),
            "{dump}"
        );
        assert!(dump.contains("table-set-list"), "{dump}");
        assert!(!dump.contains("unstructured summary=set-list"), "{dump}");
        assert!(
            proto
                .body
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, HirStmt::CallStmt(_))),
            "{dump}"
        );
    }

    #[test]
    fn folds_stable_table_build_region_back_into_constructor_with_ordered_fields() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::NewTable(unluac::transformer::NewTableInstr { dst: Reg(0) }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(1),
                value: ConstRef(0),
            }),
            LowInstr::SetTable(unluac::transformer::SetTableInstr {
                base: AccessBase::Reg(Reg(0)),
                key: AccessKey::Const(ConstRef(1)),
                value: ValueOperand::Reg(Reg(1)),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(2),
                value: ConstRef(2),
            }),
            LowInstr::SetList(unluac::transformer::SetListInstr {
                base: Reg(0),
                values: ValuePack::Fixed(RegRange::new(Reg(2), 1)),
                start_index: 1,
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let proto = &hir.protos[0];
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());

        let table = proto
            .body
            .stmts
            .iter()
            .find_map(find_table_constructor_in_stmt)
            .unwrap_or_else(|| {
                panic!("expected stable constructor region to collapse into a table constructor\n{dump}")
            });

        assert_eq!(table.fields.len(), 2, "{dump}");
        assert!(table.trailing_multivalue.is_none(), "{dump}");
        assert!(
            matches!(
                table.fields.as_slice(),
                [
                    HirTableField::Record(field),
                    HirTableField::Array(HirExpr::Integer(0))
                ] if matches!(&field.key, HirTableKey::Name(name) if name == "print")
                    && matches!(&field.value, HirExpr::Integer(41))
            ),
            "{dump}"
        );
        assert!(!dump.contains("table-set-list"), "{dump}");
    }

    #[test]
    fn folds_open_set_list_tail_into_constructor_trailing_multivalue() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::NewTable(unluac::transformer::NewTableInstr { dst: Reg(0) }),
            LowInstr::GetTable(unluac::transformer::GetTableInstr {
                dst: Reg(1),
                base: AccessBase::Env,
                key: AccessKey::Const(ConstRef(1)),
            }),
            LowInstr::Call(unluac::transformer::CallInstr {
                callee: Reg(1),
                args: ValuePack::Fixed(RegRange::new(Reg(2), 0)),
                results: ResultPack::Open(Reg(2)),
                kind: unluac::transformer::CallKind::Normal,
            }),
            LowInstr::SetList(unluac::transformer::SetListInstr {
                base: Reg(0),
                values: ValuePack::Open(Reg(2)),
                start_index: 1,
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let proto = &hir.protos[0];
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());

        let table = proto
            .body
            .stmts
            .iter()
            .find_map(find_table_constructor_in_stmt)
            .unwrap_or_else(|| {
                panic!("expected open set-list to fold into constructor trailing tail\n{dump}")
            });

        assert!(table.fields.is_empty(), "{dump}");
        assert!(
            matches!(
                table.trailing_multivalue.as_ref(),
                Some(HirExpr::Call(call))
                    if call.multiret
                        && call.args.is_empty()
                        && matches!(&call.callee, HirExpr::GlobalRef(global) if global.name == "print")
            ),
            "{dump}"
        );
        assert!(!dump.contains("table-set-list"), "{dump}");
    }

    #[test]
    fn lowers_simple_branching_proto_into_if_else() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(0),
                value: true,
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(0))),
                    negated: false,
                },
                then_target: InstrRef(4),
                else_target: InstrRef(2),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(1),
                value: ConstRef(0),
            }),
            LowInstr::Jump(unluac::transformer::JumpInstr {
                target: InstrRef(5),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(1),
                value: ConstRef(1),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(1), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let proto = &hir.protos[0];
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());
        println!("{dump}");

        assert!(matches!(
            proto.body.stmts.as_slice(),
            [
                HirStmt::Assign(_) | HirStmt::LocalDecl(_),
                HirStmt::If(if_stmt),
                HirStmt::Return(_)
            ]
                if matches!(&if_stmt.cond, expr if is_var_ref(expr))
                    && if_stmt.else_block.is_some()
        ));
        assert!(dump.contains("\n    if t0\n") || dump.contains("\n    if l0\n"));
        assert!(dump.contains("\n      then\n"));
        assert!(dump.contains("\n      else\n"));
    }

    #[test]
    fn lowers_and_like_branch_chain_into_logical_and_if_else() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(0),
                value: true,
            }),
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(1),
                value: true,
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(0))),
                    negated: true,
                },
                then_target: InstrRef(5),
                else_target: InstrRef(3),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(1))),
                    negated: true,
                },
                then_target: InstrRef(5),
                else_target: InstrRef(4),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 0)),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 0)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let proto = &hir.protos[0];
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());

        assert!(
            matches!(
                proto.body.stmts.as_slice(),
                [
                    HirStmt::Assign(_) | HirStmt::LocalDecl(_),
                    HirStmt::Assign(_) | HirStmt::LocalDecl(_),
                    HirStmt::If(if_stmt)
                ]
                    if matches!(&if_stmt.cond, HirExpr::LogicalAnd(_))
                        && if_stmt.else_block.as_ref().is_some_and(|else_block| {
                            matches!(else_block.stmts.as_slice(), [HirStmt::Return(ret)] if ret.values.is_empty())
                        })
                        && matches!(if_stmt.then_block.stmts.as_slice(), [HirStmt::Return(ret)] if ret.values.is_empty())
            ),
            "{dump}"
        );
        assert!(dump.contains("and"), "{dump}");
        assert!(
            dump.contains("if (t0 and t1)") || dump.contains("if (l0 and l1)"),
            "{dump}"
        );
    }

    #[test]
    fn lowers_or_like_value_merge_into_logical_or_expression() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::GetTable(unluac::transformer::GetTableInstr {
                dst: Reg(0),
                base: AccessBase::Env,
                key: AccessKey::Const(ConstRef(1)),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(0))),
                    negated: false,
                },
                then_target: InstrRef(3),
                else_target: InstrRef(2),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(0),
                value: ConstRef(0),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let proto = &hir.protos[0];
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());

        assert!(
            matches!(
                proto.body.stmts.last(),
                Some(HirStmt::Return(ret))
                    if matches!(
                        ret.values.as_slice(),
                        [HirExpr::LogicalOr(logical)]
                            if matches!(&logical.lhs, HirExpr::GlobalRef(global) if global.name == "print")
                                && matches!(&logical.rhs, HirExpr::Integer(41))
                    )
            ),
            "{dump}"
        );
        assert!(
            !proto
                .body
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, HirStmt::If(_))),
            "{dump}"
        );
        assert!(dump.contains("return (global(print) or 41)"), "{dump}");
    }

    #[test]
    fn lowers_and_like_value_merge_into_logical_and_expression() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::GetTable(unluac::transformer::GetTableInstr {
                dst: Reg(0),
                base: AccessBase::Env,
                key: AccessKey::Const(ConstRef(1)),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(0))),
                    negated: true,
                },
                then_target: InstrRef(3),
                else_target: InstrRef(2),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(0),
                value: ConstRef(0),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let proto = &hir.protos[0];
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());

        assert!(
            matches!(
                proto.body.stmts.last(),
                Some(HirStmt::Return(ret))
                    if matches!(
                        ret.values.as_slice(),
                        [HirExpr::LogicalAnd(logical)]
                            if matches!(&logical.lhs, HirExpr::GlobalRef(global) if global.name == "print")
                                && matches!(&logical.rhs, HirExpr::Integer(41))
                    )
            ),
            "{dump}"
        );
        assert!(
            !proto
                .body
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, HirStmt::If(_))),
            "{dump}"
        );
        assert!(dump.contains("return (global(print) and 41)"), "{dump}");
    }

    #[test]
    fn lowers_shared_fallback_value_merge_without_unstructured_fallback() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(0),
                value: true,
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(0))),
                    negated: false,
                },
                then_target: InstrRef(2),
                else_target: InstrRef(4),
            }),
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(0),
                value: true,
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(0))),
                    negated: false,
                },
                then_target: InstrRef(8),
                else_target: InstrRef(4),
            }),
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(0),
                value: true,
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(0))),
                    negated: false,
                },
                then_target: InstrRef(6),
                else_target: InstrRef(8),
            }),
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(0),
                value: false,
            }),
            LowInstr::Jump(unluac::transformer::JumpInstr {
                target: InstrRef(8),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let proto = &hir.protos[0];
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());

        assert!(
            !proto
                .body
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, HirStmt::Unstructured(_))),
            "{dump}"
        );
        assert!(
            matches!(proto.body.stmts.last(), Some(HirStmt::Return(_))),
            "{dump}"
        );
        assert!(!dump.contains("decision("), "{dump}");
    }

    #[test]
    fn lowers_nested_shared_short_circuit_value_merge_without_fallback() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(0),
                value: true,
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(0))),
                    negated: false,
                },
                then_target: InstrRef(2),
                else_target: InstrRef(8),
            }),
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(0),
                value: false,
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(0))),
                    negated: false,
                },
                then_target: InstrRef(6),
                else_target: InstrRef(4),
            }),
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(0),
                value: true,
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(0))),
                    negated: false,
                },
                then_target: InstrRef(6),
                else_target: InstrRef(8),
            }),
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(0),
                value: true,
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(0))),
                    negated: false,
                },
                then_target: InstrRef(10),
                else_target: InstrRef(8),
            }),
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(0),
                value: false,
            }),
            LowInstr::Jump(unluac::transformer::JumpInstr {
                target: InstrRef(10),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let proto = &hir.protos[0];
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());

        assert!(
            !proto
                .body
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, HirStmt::Unstructured(_))),
            "{dump}"
        );
        assert!(
            matches!(proto.body.stmts.last(), Some(HirStmt::Return(_))),
            "{dump}"
        );
        assert!(!dump.contains("decision("), "{dump}");
    }

    #[test]
    fn lowers_side_effecting_value_merge_into_structured_ifs() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(0),
                value: true,
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(0))),
                    negated: false,
                },
                then_target: InstrRef(2),
                else_target: InstrRef(5),
            }),
            LowInstr::GetTable(unluac::transformer::GetTableInstr {
                dst: Reg(1),
                base: AccessBase::Env,
                key: AccessKey::Const(ConstRef(1)),
            }),
            LowInstr::Call(unluac::transformer::CallInstr {
                callee: Reg(1),
                args: ValuePack::Fixed(RegRange::new(Reg(2), 0)),
                results: unluac::transformer::ResultPack::Fixed(RegRange::new(Reg(1), 1)),
                kind: unluac::transformer::CallKind::Normal,
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(1))),
                    negated: false,
                },
                then_target: InstrRef(7),
                else_target: InstrRef(5),
            }),
            LowInstr::GetTable(unluac::transformer::GetTableInstr {
                dst: Reg(1),
                base: AccessBase::Env,
                key: AccessKey::Const(ConstRef(1)),
            }),
            LowInstr::Call(unluac::transformer::CallInstr {
                callee: Reg(1),
                args: ValuePack::Fixed(RegRange::new(Reg(2), 0)),
                results: unluac::transformer::ResultPack::Fixed(RegRange::new(Reg(1), 1)),
                kind: unluac::transformer::CallKind::Normal,
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(1), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let proto = &hir.protos[0];
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());

        assert!(!dump.contains("unstructured summary=fallback"), "{dump}");
        assert!(!dump.contains("unresolved(phi"), "{dump}");
        assert!(dump.contains("call(normal)"), "{dump}");
        assert!(
            proto
                .body
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, HirStmt::If(_))),
            "{dump}"
        );
        assert!(dump.contains("if t0") || dump.contains("if l0"), "{dump}");
        assert!(
            dump.contains("return t5") || dump.contains("local [\"l1\"] = -"),
            "{dump}"
        );
        assert!(
            dump.contains("return t5") || dump.contains("return l1"),
            "{dump}"
        );
    }

    #[test]
    fn lowers_multi_use_value_merge_into_conditional_reassign() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::GetTable(unluac::transformer::GetTableInstr {
                dst: Reg(0),
                base: AccessBase::Env,
                key: AccessKey::Const(ConstRef(1)),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(0))),
                    negated: false,
                },
                then_target: InstrRef(3),
                else_target: InstrRef(2),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(0),
                value: ConstRef(0),
            }),
            LowInstr::Move(MoveInstr {
                dst: Reg(1),
                src: Reg(0),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 2)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let proto = &hir.protos[0];
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());

        assert!(
            matches!(
                proto.body.stmts.as_slice(),
                [
                    HirStmt::LocalDecl(local_decl),
                    HirStmt::If(_),
                    HirStmt::Return(ret),
                ] if matches!(&local_decl.bindings.as_slice(), [LocalId(_)])
                    && matches!(
                        &local_decl.values.as_slice(),
                        [HirExpr::GlobalRef(global)] if global.name == "print"
                    )
                    && matches!(ret.values.as_slice(), [HirExpr::LocalRef(_), HirExpr::LocalRef(_)])
            ),
            "{dump}"
        );
        assert!(
            proto
                .body
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, HirStmt::If(_))),
            "{dump}"
        );
        assert!(
            dump.contains("local [\"") || dump.contains("local ["),
            "{dump}"
        );
        assert!(dump.contains("if (not l0)"), "{dump}");
        assert!(dump.contains("return l0, l0"), "{dump}");
    }

    #[test]
    fn lowers_plain_branch_value_merge_without_unresolved_phi() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(0),
                value: true,
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(0))),
                    negated: false,
                },
                then_target: InstrRef(2),
                else_target: InstrRef(4),
            }),
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(1),
                value: true,
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(5),
            }),
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(1),
                value: false,
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(1), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());

        assert!(!dump.contains("unresolved(phi"), "{dump}");
        assert!(!dump.contains("decision("), "{dump}");
    }

    #[test]
    fn lowers_reducible_while_loop_into_hir_while() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(0),
                value: ConstRef(2),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(1),
                value: ConstRef(3),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Le,
                    operands: BranchOperands::Binary(
                        unluac::transformer::CondOperand::Reg(Reg(1)),
                        unluac::transformer::CondOperand::Const(ConstRef(4)),
                    ),
                    negated: true,
                },
                then_target: InstrRef(6),
                else_target: InstrRef(3),
            }),
            LowInstr::BinaryOp(BinaryOpInstr {
                dst: Reg(0),
                op: BinaryOpKind::Add,
                lhs: ValueOperand::Reg(Reg(0)),
                rhs: ValueOperand::Reg(Reg(1)),
            }),
            LowInstr::BinaryOp(BinaryOpInstr {
                dst: Reg(1),
                op: BinaryOpKind::Add,
                lhs: ValueOperand::Reg(Reg(1)),
                rhs: ValueOperand::Const(ConstRef(3)),
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(2),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());
        let proto = &hir.protos[0];

        assert!(
            matches!(
                proto.body.stmts.as_slice(),
                [
                    HirStmt::LocalDecl(_),
                    HirStmt::LocalDecl(_),
                    HirStmt::While(_),
                    HirStmt::Return(_),
                ]
            ),
            "{dump}"
        );
        assert!(dump.contains("\n    while "), "{dump}");
        assert!(dump.contains("assign l0 = (l0 + l1)"), "{dump}");
    }

    #[test]
    fn lowers_reducible_repeat_loop_into_hir_repeat() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(0),
                value: ConstRef(2),
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(2),
            }),
            LowInstr::BinaryOp(BinaryOpInstr {
                dst: Reg(0),
                op: BinaryOpKind::Add,
                lhs: ValueOperand::Reg(Reg(0)),
                rhs: ValueOperand::Const(ConstRef(3)),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Le,
                    operands: BranchOperands::Binary(
                        unluac::transformer::CondOperand::Const(ConstRef(4)),
                        unluac::transformer::CondOperand::Reg(Reg(0)),
                    ),
                    negated: true,
                },
                then_target: InstrRef(2),
                else_target: InstrRef(4),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());
        let proto = &hir.protos[0];

        assert!(
            matches!(
                proto.body.stmts.as_slice(),
                [
                    HirStmt::LocalDecl(_),
                    HirStmt::Repeat(_),
                    HirStmt::Return(_)
                ]
            ),
            "{dump}"
        );
        assert!(dump.contains("\n    repeat\n"), "{dump}");
        assert!(dump.contains("assign l0 = (l0 + 1)"), "{dump}");
        assert!(dump.contains("until (3 <= l0)"), "{dump}");
    }

    #[test]
    fn lowers_repeat_loop_even_with_unreachable_outside_predecessor() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(0),
                value: ConstRef(2),
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(3),
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(3),
            }),
            LowInstr::BinaryOp(BinaryOpInstr {
                dst: Reg(0),
                op: BinaryOpKind::Add,
                lhs: ValueOperand::Reg(Reg(0)),
                rhs: ValueOperand::Const(ConstRef(3)),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Le,
                    operands: BranchOperands::Binary(
                        unluac::transformer::CondOperand::Const(ConstRef(4)),
                        unluac::transformer::CondOperand::Reg(Reg(0)),
                    ),
                    negated: true,
                },
                then_target: InstrRef(3),
                else_target: InstrRef(5),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());

        assert!(dump.contains("\n    repeat\n"), "{dump}");
        assert!(!dump.contains("unstructured summary=fallback"), "{dump}");
        assert!(!dump.contains("unresolved(phi"), "{dump}");
    }

    #[test]
    fn lowers_repeat_break_check_that_targets_continue_block_without_fallback() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(0),
                value: ConstRef(2),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(1),
                value: ConstRef(2),
            }),
            LowInstr::BinaryOp(BinaryOpInstr {
                dst: Reg(0),
                op: BinaryOpKind::Add,
                lhs: ValueOperand::Reg(Reg(0)),
                rhs: ValueOperand::Const(ConstRef(3)),
            }),
            LowInstr::BinaryOp(BinaryOpInstr {
                dst: Reg(1),
                op: BinaryOpKind::Add,
                lhs: ValueOperand::Reg(Reg(1)),
                rhs: ValueOperand::Reg(Reg(0)),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Eq,
                    operands: BranchOperands::Binary(
                        unluac::transformer::CondOperand::Reg(Reg(0)),
                        unluac::transformer::CondOperand::Const(ConstRef(4)),
                    ),
                    negated: false,
                },
                then_target: InstrRef(6),
                else_target: InstrRef(5),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Le,
                    operands: BranchOperands::Binary(
                        unluac::transformer::CondOperand::Const(ConstRef(5)),
                        unluac::transformer::CondOperand::Reg(Reg(0)),
                    ),
                    negated: true,
                },
                then_target: InstrRef(2),
                else_target: InstrRef(7),
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(7),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 2)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());
        let proto = &hir.protos[0];

        assert!(
            matches!(
                proto.body.stmts.as_slice(),
                [
                    HirStmt::LocalDecl(_),
                    HirStmt::LocalDecl(_),
                    HirStmt::Repeat(_),
                    HirStmt::Return(_),
                ]
            ),
            "{dump}"
        );
        assert!(dump.contains("\n    repeat\n"), "{dump}");
        assert!(dump.contains("\n        then\n          break\n"), "{dump}");
        assert!(!dump.contains("unstructured summary=fallback"), "{dump}");
        assert!(!dump.contains("unresolved(phi"), "{dump}");
    }

    #[test]
    fn lowers_repeat_break_pad_that_skips_linear_post_loop_pad() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(0),
                value: ConstRef(2),
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(2),
            }),
            LowInstr::BinaryOp(BinaryOpInstr {
                dst: Reg(0),
                op: BinaryOpKind::Add,
                lhs: ValueOperand::Reg(Reg(0)),
                rhs: ValueOperand::Const(ConstRef(3)),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Eq,
                    operands: BranchOperands::Binary(
                        unluac::transformer::CondOperand::Reg(Reg(0)),
                        unluac::transformer::CondOperand::Const(ConstRef(5)),
                    ),
                    negated: false,
                },
                then_target: InstrRef(5),
                else_target: InstrRef(4),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Le,
                    operands: BranchOperands::Binary(
                        unluac::transformer::CondOperand::Const(ConstRef(6)),
                        unluac::transformer::CondOperand::Reg(Reg(0)),
                    ),
                    negated: true,
                },
                then_target: InstrRef(2),
                else_target: InstrRef(6),
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(7),
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(7),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());

        assert!(dump.contains("\n    repeat\n"), "{dump}");
        assert!(dump.contains("\n        then\n          break\n"), "{dump}");
        assert!(!dump.contains("unstructured summary=fallback"), "{dump}");
        assert!(!dump.contains("unresolved(phi"), "{dump}");
    }

    #[test]
    fn rewrites_repeat_condition_with_body_promoted_local() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(0),
                value: ConstRef(2),
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(2),
            }),
            LowInstr::BinaryOp(BinaryOpInstr {
                dst: Reg(0),
                op: BinaryOpKind::Add,
                lhs: ValueOperand::Reg(Reg(0)),
                rhs: ValueOperand::Const(ConstRef(3)),
            }),
            LowInstr::BinaryOp(BinaryOpInstr {
                dst: Reg(1),
                op: BinaryOpKind::Mul,
                lhs: ValueOperand::Reg(Reg(0)),
                rhs: ValueOperand::Const(ConstRef(4)),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Lt,
                    operands: BranchOperands::Binary(
                        unluac::transformer::CondOperand::Const(ConstRef(5)),
                        unluac::transformer::CondOperand::Reg(Reg(1)),
                    ),
                    negated: true,
                },
                then_target: InstrRef(7),
                else_target: InstrRef(5),
            }),
            LowInstr::BinaryOp(BinaryOpInstr {
                dst: Reg(2),
                op: BinaryOpKind::Mod,
                lhs: ValueOperand::Reg(Reg(0)),
                rhs: ValueOperand::Const(ConstRef(4)),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Eq,
                    operands: BranchOperands::Binary(
                        unluac::transformer::CondOperand::Reg(Reg(2)),
                        unluac::transformer::CondOperand::Const(ConstRef(2)),
                    ),
                    negated: true,
                },
                then_target: InstrRef(7),
                else_target: InstrRef(8),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Lt,
                    operands: BranchOperands::Binary(
                        unluac::transformer::CondOperand::Const(ConstRef(6)),
                        unluac::transformer::CondOperand::Reg(Reg(1)),
                    ),
                    negated: true,
                },
                then_target: InstrRef(2),
                else_target: InstrRef(9),
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(9),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());

        assert!(dump.contains("\n    repeat\n"), "{dump}");
        assert!(!dump.contains("until (6 < t"), "{dump}");
        assert!(dump.contains("until (6 < l1)"), "{dump}");
    }

    #[test]
    fn lowers_reducible_numeric_for_into_hir_numeric_for() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(0),
                value: ConstRef(2),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(2),
                value: ConstRef(5),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(3),
                value: ConstRef(6),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(4),
                value: ConstRef(3),
            }),
            LowInstr::NumericForInit(NumericForInitInstr {
                index: Reg(2),
                limit: Reg(3),
                step: Reg(4),
                binding: Reg(5),
                body_target: InstrRef(5),
                exit_target: InstrRef(7),
            }),
            LowInstr::BinaryOp(BinaryOpInstr {
                dst: Reg(0),
                op: BinaryOpKind::Add,
                lhs: ValueOperand::Reg(Reg(0)),
                rhs: ValueOperand::Reg(Reg(5)),
            }),
            LowInstr::NumericForLoop(NumericForLoopInstr {
                index: Reg(2),
                limit: Reg(3),
                step: Reg(4),
                binding: Reg(5),
                body_target: InstrRef(5),
                exit_target: InstrRef(7),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());
        let proto = &hir.protos[0];

        assert!(
            matches!(
                proto.body.stmts.as_slice(),
                [
                    HirStmt::LocalDecl(_),
                    HirStmt::LocalDecl(_),
                    HirStmt::LocalDecl(_),
                    HirStmt::LocalDecl(_),
                    HirStmt::NumericFor(_),
                    HirStmt::Return(_),
                ]
            ),
            "{dump}"
        );
        assert!(dump.contains("numeric-for l0 = l2, l3, l4"), "{dump}");
        assert!(dump.contains("assign l1 = (l1 + l0)"), "{dump}");
    }

    #[test]
    fn keeps_branch_state_updates_inside_numeric_for_body_when_merge_is_loop_continue() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(0),
                value: ConstRef(2),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(1),
                value: ConstRef(3),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(2),
                value: ConstRef(4),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(3),
                value: ConstRef(3),
            }),
            LowInstr::NumericForInit(NumericForInitInstr {
                index: Reg(1),
                limit: Reg(2),
                step: Reg(3),
                binding: Reg(4),
                body_target: InstrRef(5),
                exit_target: InstrRef(10),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Eq,
                    operands: BranchOperands::Binary(
                        unluac::transformer::CondOperand::Reg(Reg(4)),
                        unluac::transformer::CondOperand::Const(ConstRef(3)),
                    ),
                    negated: false,
                },
                then_target: InstrRef(8),
                else_target: InstrRef(6),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(0),
                value: ConstRef(2),
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(9),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(0),
                value: ConstRef(3),
            }),
            LowInstr::NumericForLoop(NumericForLoopInstr {
                index: Reg(1),
                limit: Reg(2),
                step: Reg(3),
                binding: Reg(4),
                body_target: InstrRef(5),
                exit_target: InstrRef(10),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());

        assert!(dump.contains("numeric-for l0 ="), "{dump}");
        assert!(dump.contains("\n      if "), "{dump}");
        assert!(!dump.contains("unresolved(phi"), "{dump}");
        assert!(
            dump.contains("assign t") || dump.contains("assign l"),
            "{dump}"
        );
    }

    #[test]
    fn lowers_multi_exit_numeric_for_with_break_into_hir_numeric_for() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(1),
                value: ConstRef(3),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(2),
                value: ConstRef(5),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(3),
                value: ConstRef(3),
            }),
            LowInstr::NumericForInit(NumericForInitInstr {
                index: Reg(1),
                limit: Reg(2),
                step: Reg(3),
                binding: Reg(4),
                body_target: InstrRef(4),
                exit_target: InstrRef(7),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Eq,
                    operands: BranchOperands::Binary(
                        unluac::transformer::CondOperand::Reg(Reg(4)),
                        unluac::transformer::CondOperand::Const(ConstRef(4)),
                    ),
                    negated: true,
                },
                then_target: InstrRef(6),
                else_target: InstrRef(5),
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(7),
            }),
            LowInstr::NumericForLoop(NumericForLoopInstr {
                index: Reg(1),
                limit: Reg(2),
                step: Reg(3),
                binding: Reg(4),
                body_target: InstrRef(4),
                exit_target: InstrRef(7),
            }),
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(0),
                value: true,
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());
        let proto = &hir.protos[0];

        assert!(
            matches!(
                proto.body.stmts.as_slice(),
                [
                    HirStmt::LocalDecl(_),
                    HirStmt::LocalDecl(_),
                    HirStmt::LocalDecl(_),
                    HirStmt::NumericFor(_),
                    HirStmt::Return(_),
                ]
            ),
            "{dump}"
        );
        assert!(dump.contains("numeric-for l0 = l1, l2, l3"), "{dump}");
        assert!(dump.contains("\n        then\n          break\n"), "{dump}");
        assert!(!dump.contains("unstructured summary=fallback"), "{dump}");
        assert!(!dump.contains("unresolved("), "{dump}");
    }

    #[test]
    fn lowers_multi_exit_while_with_break_pad_into_hir_while_and_break() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(0),
                value: ConstRef(2),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Lt,
                    operands: BranchOperands::Binary(
                        unluac::transformer::CondOperand::Reg(Reg(0)),
                        unluac::transformer::CondOperand::Const(ConstRef(5)),
                    ),
                    negated: true,
                },
                then_target: InstrRef(8),
                else_target: InstrRef(2),
            }),
            LowInstr::BinaryOp(BinaryOpInstr {
                dst: Reg(0),
                op: BinaryOpKind::Add,
                lhs: ValueOperand::Reg(Reg(0)),
                rhs: ValueOperand::Const(ConstRef(3)),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Eq,
                    operands: BranchOperands::Binary(
                        unluac::transformer::CondOperand::Reg(Reg(0)),
                        unluac::transformer::CondOperand::Const(ConstRef(4)),
                    ),
                    negated: true,
                },
                then_target: InstrRef(6),
                else_target: InstrRef(4),
            }),
            LowInstr::Close(unluac::transformer::CloseInstr { from: Reg(1) }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(8),
            }),
            LowInstr::Close(unluac::transformer::CloseInstr { from: Reg(1) }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(1),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());
        let proto = &hir.protos[0];

        assert!(
            matches!(
                proto.body.stmts.as_slice(),
                [HirStmt::LocalDecl(_), HirStmt::While(_), HirStmt::Return(_),]
            ),
            "{dump}"
        );
        assert!(dump.contains("\n    while "), "{dump}");
        assert!(dump.contains("assign l0 = (l0 + 1)"), "{dump}");
        assert!(dump.contains("if (l0 == 3)"), "{dump}");
        assert!(dump.contains("\n          break\n"), "{dump}");
        assert!(!dump.contains("unstructured summary=close"), "{dump}");
    }

    #[test]
    fn lowers_reducible_generic_for_into_hir_generic_for() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(0),
                value: ConstRef(0),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(2),
                value: ConstRef(2),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(3),
                value: ConstRef(3),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(4),
                value: ConstRef(4),
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(6),
            }),
            LowInstr::BinaryOp(BinaryOpInstr {
                dst: Reg(0),
                op: BinaryOpKind::Add,
                lhs: ValueOperand::Reg(Reg(0)),
                rhs: ValueOperand::Reg(Reg(5)),
            }),
            LowInstr::GenericForCall(GenericForCallInstr {
                state: RegRange::new(Reg(2), 3),
                results: ResultPack::Fixed(RegRange::new(Reg(5), 2)),
            }),
            LowInstr::GenericForLoop(GenericForLoopInstr {
                control: Reg(4),
                bindings: RegRange::new(Reg(5), 2),
                body_target: InstrRef(5),
                exit_target: InstrRef(8),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());
        let proto = &hir.protos[0];

        assert!(
            matches!(
                proto.body.stmts.as_slice(),
                [
                    HirStmt::LocalDecl(_),
                    HirStmt::LocalDecl(_),
                    HirStmt::LocalDecl(_),
                    HirStmt::LocalDecl(_),
                    HirStmt::GenericFor(_),
                    HirStmt::Return(_),
                ]
            ),
            "{dump}"
        );
        assert!(dump.contains("generic-for l0, l1 in"), "{dump}");
        assert!(dump.contains("assign l2 = (l2 + l0)"), "{dump}");
    }

    #[test]
    fn lowers_generic_for_with_loop_local_continue_and_terminal_exit_without_fallback() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(1),
                value: ConstRef(2),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(2),
                value: ConstRef(2),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(3),
                value: ConstRef(3),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(4),
                value: ConstRef(5),
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(10),
            }),
            LowInstr::Move(MoveInstr {
                dst: Reg(7),
                src: Reg(5),
            }),
            LowInstr::Move(MoveInstr {
                dst: Reg(8),
                src: Reg(6),
            }),
            LowInstr::BinaryOp(BinaryOpInstr {
                dst: Reg(1),
                op: BinaryOpKind::Add,
                lhs: ValueOperand::Reg(Reg(1)),
                rhs: ValueOperand::Reg(Reg(7)),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Lt,
                    operands: BranchOperands::Binary(
                        unluac::transformer::CondOperand::Const(ConstRef(6)),
                        unluac::transformer::CondOperand::Reg(Reg(1)),
                    ),
                    negated: true,
                },
                then_target: InstrRef(9),
                else_target: InstrRef(10),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(7), 2)),
            }),
            LowInstr::GenericForCall(GenericForCallInstr {
                state: RegRange::new(Reg(2), 3),
                results: ResultPack::Fixed(RegRange::new(Reg(5), 2)),
            }),
            LowInstr::GenericForLoop(GenericForLoopInstr {
                control: Reg(4),
                bindings: RegRange::new(Reg(5), 2),
                body_target: InstrRef(5),
                exit_target: InstrRef(12),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(1), 1)),
            }),
        ]);

        let hir = analyze_fixture(&chunk);
        let dump = dump_hir(&hir, DebugDetail::Normal, &Default::default());
        let proto = &hir.protos[0];

        assert!(
            !proto
                .body
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, HirStmt::Unstructured(_))),
            "{dump}"
        );
        assert!(
            matches!(
                proto.body.stmts.as_slice(),
                [
                    HirStmt::LocalDecl(_),
                    HirStmt::LocalDecl(_),
                    HirStmt::LocalDecl(_),
                    HirStmt::LocalDecl(_),
                    HirStmt::GenericFor(_),
                    HirStmt::Return(_),
                ]
            ),
            "{dump}"
        );
        assert!(
            matches!(
                &proto.body.stmts[4],
                HirStmt::GenericFor(generic_for)
                    if matches!(
                        generic_for.body.stmts.as_slice(),
                        [
                            HirStmt::LocalDecl(_),
                            HirStmt::LocalDecl(_),
                            HirStmt::Assign(_),
                            HirStmt::If(if_stmt),
                        ] if matches!(if_stmt.then_block.stmts.as_slice(), [HirStmt::Continue])
                            && if_stmt
                                .else_block
                                .as_ref()
                                .is_some_and(|else_block| matches!(else_block.stmts.as_slice(), [HirStmt::Return(_)]))
                    )
            ),
            "{dump}"
        );
        assert!(dump.contains("generic-for l0, l1 in"), "{dump}");
        assert!(dump.contains("\n          continue\n"), "{dump}");
    }
}

fn analyze_fixture(chunk: &LoweredChunk) -> unluac::hir::HirModule {
    let cfg = build_cfg_graph(chunk);
    let graph_facts = analyze_graph_facts(&cfg);
    let dataflow = analyze_dataflow(chunk, &cfg, &graph_facts);
    let structure = analyze_structure(chunk, &cfg, &graph_facts, &dataflow);
    analyze_hir(chunk, &cfg, &graph_facts, &dataflow, &structure)
}

fn chunk_with_instrs(instrs: Vec<LowInstr>) -> LoweredChunk {
    LoweredChunk {
        header: ChunkHeader {
            dialect: Dialect::PucLua,
            version: DialectVersion::Lua51,
            format: 0,
            endianness: Endianness::Little,
            integer_size: 4,
            size_t_size: 8,
            instruction_size: 4,
            number_size: 8,
            integral_number: false,
            extra: DialectHeaderExtra::Lua51(Lua51HeaderExtra),
            origin: dummy_origin(),
        },
        main: proto_with_instrs(instrs),
        origin: dummy_origin(),
    }
}

fn proto_with_instrs(instrs: Vec<LowInstr>) -> LoweredProto {
    LoweredProto {
        source: None,
        line_range: ProtoLineRange {
            defined_start: 0,
            defined_end: 0,
        },
        signature: ProtoSignature {
            num_params: 0,
            is_vararg: false,
        },
        frame: ProtoFrameInfo { max_stack_size: 8 },
        constants: RawConstPool {
            common: RawConstPoolCommon {
                literals: vec![
                    unluac::parser::RawLiteralConst::Integer(41),
                    unluac::parser::RawLiteralConst::String(unluac::parser::RawString {
                        bytes: b"print".to_vec(),
                        text: Some(unluac::parser::DecodedText {
                            encoding: unluac::parser::StringEncoding::Utf8,
                            value: "print".to_owned(),
                        }),
                        origin: dummy_origin(),
                    }),
                    unluac::parser::RawLiteralConst::Integer(0),
                    unluac::parser::RawLiteralConst::Integer(1),
                    unluac::parser::RawLiteralConst::Integer(3),
                    unluac::parser::RawLiteralConst::Integer(4),
                    unluac::parser::RawLiteralConst::Integer(6),
                ],
            },
            extra: DialectConstPoolExtra::Lua51(Lua51ConstPoolExtra),
        },
        upvalues: RawUpvalueInfo {
            common: RawUpvalueInfoCommon {
                count: 0,
                descriptors: Vec::new(),
            },
            extra: DialectUpvalueExtra::Lua51(Lua51UpvalueExtra),
        },
        debug_info: RawDebugInfo {
            common: RawDebugInfoCommon {
                line_info: Vec::new(),
                local_vars: Vec::new(),
                upvalue_names: Vec::new(),
            },
            extra: DialectDebugExtra::Lua51(Lua51DebugExtra),
        },
        children: Vec::new(),
        instrs,
        lowering_map: LoweringMap::default(),
        origin: dummy_origin(),
    }
}

fn dummy_origin() -> Origin {
    Origin {
        span: Span { offset: 0, size: 0 },
        raw_word: None,
    }
}
