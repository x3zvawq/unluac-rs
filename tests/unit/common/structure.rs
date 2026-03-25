//! 这些测试固定 StructureFacts 第一版候选提取的共享契约。
//!
//! 这里继续用手工 low-IR 夹具，把断言直接钉在结构候选本身，避免把问题掺回
//! parser / transformer 的其他层里。

use unluac::cfg::{analyze_dataflow, analyze_graph_facts, build_cfg_graph};
use unluac::parser::{
    ChunkHeader, Dialect, DialectConstPoolExtra, DialectDebugExtra, DialectHeaderExtra,
    DialectUpvalueExtra, DialectVersion, Endianness, Lua51ConstPoolExtra, Lua51DebugExtra,
    Lua51HeaderExtra, Lua51UpvalueExtra, Origin, ProtoFrameInfo, ProtoLineRange, ProtoSignature,
    RawConstPool, RawConstPoolCommon, RawDebugInfo, RawDebugInfoCommon, RawUpvalueInfo,
    RawUpvalueInfoCommon, Span,
};
use unluac::structure::{
    BranchKind, GotoReason, LoopKindHint, RegionKind, ScopeKind, ShortCircuitExit,
    ShortCircuitTarget, analyze_structure,
};
use unluac::transformer::{
    BinaryOpInstr, BinaryOpKind, BranchCond, BranchInstr, BranchOperands, BranchPredicate,
    CloseInstr, ConstRef, GenericForCallInstr, GenericForLoopInstr, InstrRef, JumpInstr,
    LoadBoolInstr, LoadConstInstr, LowInstr, LoweredChunk, LoweredProto, LoweringMap, MoveInstr,
    Reg, RegRange, ResultPack, ReturnInstr, ValueOperand, ValuePack,
};

mod analyze_structure_shared {
    use super::*;

    #[test]
    fn classifies_if_then_branch_and_invert_hint() {
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
            LowInstr::Move(MoveInstr {
                dst: Reg(1),
                src: Reg(0),
            }),
            LowInstr::Jump(unluac::transformer::JumpInstr {
                target: InstrRef(4),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(1), 1)),
            }),
        ]);

        let structure = analyze_fixture(&chunk);
        let branch = &structure.branch_candidates[0];

        assert_eq!(branch.header.index(), 0);
        assert_eq!(branch.kind, BranchKind::IfThen);
        assert_eq!(branch.then_entry.index(), 1);
        assert_eq!(branch.merge.map(|block| block.index()), Some(2));
        assert!(branch.invert_hint);
    }

    #[test]
    fn classifies_while_like_loop_and_loop_region() {
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
            LowInstr::Move(MoveInstr {
                dst: Reg(1),
                src: Reg(0),
            }),
            LowInstr::Jump(unluac::transformer::JumpInstr {
                target: InstrRef(1),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(1), 1)),
            }),
        ]);

        let structure = analyze_fixture(&chunk);
        let loop_candidate = &structure.loop_candidates[0];
        let loop_region = structure
            .region_facts
            .iter()
            .find(|region| region.kind == RegionKind::LoopRegion)
            .expect("while-like loop should produce a loop region");

        assert_eq!(loop_candidate.header.index(), 1);
        assert_eq!(loop_candidate.kind_hint, LoopKindHint::WhileLike);
        assert_eq!(
            loop_candidate.continue_target.map(|block| block.index()),
            Some(1)
        );
        assert!(loop_candidate.reducible);
        assert_eq!(
            loop_candidate
                .exits
                .iter()
                .map(|block| block.index())
                .collect::<Vec<_>>(),
            vec![3]
        );
        assert_eq!(loop_region.entry.index(), 1);
        assert!(loop_region.structureable);
    }

    #[test]
    fn extracts_loop_scope_from_while_like_loop() {
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
            LowInstr::Move(MoveInstr {
                dst: Reg(1),
                src: Reg(0),
            }),
            LowInstr::Jump(unluac::transformer::JumpInstr {
                target: InstrRef(1),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(1), 1)),
            }),
        ]);

        let structure = analyze_fixture(&chunk);
        let loop_scope = structure
            .scope_candidates
            .iter()
            .find(|scope| scope.kind == ScopeKind::LoopScope)
            .expect("while-like loop should produce a loop scope");

        assert_eq!(loop_scope.entry.index(), 1);
        assert_eq!(loop_scope.exit.map(|block| block.index()), Some(3));
        assert!(loop_scope.close_points.is_empty());
    }

    #[test]
    fn classifies_generic_for_like_loop_without_continue_requirement() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(2),
                value: true,
            }),
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(3),
                value: false,
            }),
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(4),
                value: true,
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(5),
            }),
            LowInstr::Move(MoveInstr {
                dst: Reg(0),
                src: Reg(5),
            }),
            LowInstr::GenericForCall(GenericForCallInstr {
                state: RegRange::new(Reg(2), 3),
                results: ResultPack::Fixed(RegRange::new(Reg(5), 2)),
            }),
            LowInstr::GenericForLoop(GenericForLoopInstr {
                control: Reg(4),
                bindings: RegRange::new(Reg(5), 2),
                body_target: InstrRef(4),
                exit_target: InstrRef(7),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let structure = analyze_fixture(&chunk);
        let loop_candidate = structure
            .loop_candidates
            .iter()
            .find(|candidate| candidate.kind_hint == LoopKindHint::GenericForLike)
            .expect("generic-for shape should be recognized");

        assert_eq!(loop_candidate.header.index(), 2);
        assert_eq!(loop_candidate.continue_target, Some(loop_candidate.header));
        assert!(loop_candidate.reducible);
        assert!(structure.goto_requirements.is_empty());
    }

    #[test]
    fn ignores_natural_fallthrough_into_repeat_continue_block() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(0),
                value: true,
            }),
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(1),
                value: true,
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(3),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(0))),
                    negated: false,
                },
                then_target: InstrRef(5),
                else_target: InstrRef(4),
            }),
            LowInstr::Move(MoveInstr {
                dst: Reg(1),
                src: Reg(0),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(1))),
                    negated: true,
                },
                then_target: InstrRef(3),
                else_target: InstrRef(6),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 0)),
            }),
        ]);

        let structure = analyze_fixture(&chunk);
        let loop_candidate = structure
            .loop_candidates
            .iter()
            .find(|candidate| candidate.kind_hint == LoopKindHint::RepeatLike)
            .expect("repeat-like loop should be recognized");

        let continue_like_requirements = structure
            .goto_requirements
            .iter()
            .filter(|requirement| requirement.reason == GotoReason::UnstructuredContinueLike)
            .collect::<Vec<_>>();

        assert_eq!(loop_candidate.header.index(), 1);
        assert_eq!(
            loop_candidate.continue_target.map(|block| block.index()),
            Some(3)
        );
        assert_eq!(continue_like_requirements.len(), 1);
        assert_eq!(continue_like_requirements[0].from.index(), 1);
        assert_eq!(continue_like_requirements[0].to.index(), 3);
    }

    #[test]
    fn extracts_or_like_short_circuit_at_phi_merge() {
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
                then_target: InstrRef(3),
                else_target: InstrRef(2),
            }),
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(0),
                value: false,
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let structure = analyze_fixture(&chunk);
        let candidate = structure
            .short_circuit_candidates
            .iter()
            .find(|candidate| {
                candidate.header.index() == 0
                    && matches!(candidate.exit, ShortCircuitExit::ValueMerge(_))
            })
            .expect("or-like lowering should produce a short-circuit candidate");

        assert!(matches!(candidate.exit, ShortCircuitExit::ValueMerge(_)));
        assert_eq!(candidate.entry.index(), 0);
        assert_eq!(candidate.nodes.len(), 1);
        assert_eq!(candidate.result_reg, Some(Reg(0)));
        assert!(matches!(
            (&candidate.nodes[0].truthy, &candidate.nodes[0].falsy),
            (ShortCircuitTarget::Value(block), ShortCircuitTarget::Value(other))
                if block.index() == 0 && other.index() == 1
        ));
        assert!(candidate.reducible);
    }

    #[test]
    fn classifies_terminal_if_else_without_merge() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(0),
                value: true,
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
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 0)),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 0)),
            }),
        ]);

        let structure = analyze_fixture(&chunk);
        let branch = structure
            .branch_candidates
            .iter()
            .find(|candidate| candidate.header.index() == 0)
            .expect("terminal branch should still produce a branch candidate");
        let mut exits = vec![
            branch.then_entry.index(),
            branch
                .else_entry
                .expect("terminal if-else should keep both exits")
                .index(),
        ];
        exits.sort_unstable();

        assert_eq!(branch.kind, BranchKind::IfElse);
        assert_eq!(branch.merge, None);
        assert_eq!(exits, vec![1, 2]);
    }

    #[test]
    fn extracts_branch_value_merge_candidate_at_if_else_join() {
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

        let structure = analyze_fixture(&chunk);
        let candidate = structure
            .branch_value_merge_candidates
            .iter()
            .find(|candidate| candidate.header.index() == 0)
            .expect("if-else join should produce a branch value merge candidate");
        let value = candidate
            .values
            .iter()
            .find(|value| value.reg == Reg(1))
            .expect("merged result register should be tracked");

        assert_eq!(candidate.merge.index(), 3);
        assert_eq!(
            value
                .then_preds
                .iter()
                .map(|block| block.index())
                .collect::<Vec<_>>(),
            vec![1]
        );
        assert_eq!(
            value
                .else_preds
                .iter()
                .map(|block| block.index())
                .collect::<Vec<_>>(),
            vec![2]
        );
    }

    #[test]
    fn extracts_and_like_short_circuit_branch_exit() {
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

        let structure = analyze_fixture(&chunk);
        let candidate = structure
            .short_circuit_candidates
            .iter()
            .find(|candidate| candidate.header.index() == 0)
            .expect("terminal and-like chain should produce a branch-exit short-circuit");

        assert!(matches!(
            candidate.exit,
            ShortCircuitExit::BranchExit { truthy, falsy }
                if truthy.index() == 2 && falsy.index() == 3
        ));
        assert_eq!(candidate.entry.index(), 0);
        assert_eq!(candidate.nodes.len(), 2);
        assert_eq!(candidate.result_reg, None);
        assert!(matches!(
            (&candidate.nodes[0].truthy, &candidate.nodes[0].falsy),
            (ShortCircuitTarget::Node(node_ref), ShortCircuitTarget::FalsyExit)
                if node_ref.index() == 1
        ));
        assert!(matches!(
            (&candidate.nodes[1].truthy, &candidate.nodes[1].falsy),
            (
                ShortCircuitTarget::TruthyExit,
                ShortCircuitTarget::FalsyExit
            )
        ));
        assert!(candidate.reducible);
    }

    #[test]
    fn extracts_value_merge_short_circuit_dag_with_shared_fallback() {
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

        let structure = analyze_fixture(&chunk);
        let candidate = structure
            .short_circuit_candidates
            .iter()
            .find(|candidate| {
                candidate.header.index() == 0
                    && matches!(candidate.exit, ShortCircuitExit::ValueMerge(_))
            })
            .expect("shared fallback should produce a value-merge short-circuit");

        assert!(matches!(candidate.exit, ShortCircuitExit::ValueMerge(_)));
        assert_eq!(candidate.result_reg, Some(Reg(0)));
        assert_eq!(candidate.entry.index(), 0);
        assert_eq!(candidate.nodes.len(), 3);
        assert!(matches!(
            (&candidate.nodes[0].truthy, &candidate.nodes[0].falsy),
            (ShortCircuitTarget::Node(node_ref), ShortCircuitTarget::Node(other))
                if node_ref.index() == 1 && other.index() == 2
        ));
        assert!(matches!(
            (&candidate.nodes[1].truthy, &candidate.nodes[1].falsy),
            (ShortCircuitTarget::Value(block), ShortCircuitTarget::Node(node_ref))
                if block.index() == 1 && node_ref.index() == 2
        ));
        assert!(matches!(
            (&candidate.nodes[2].truthy, &candidate.nodes[2].falsy),
            (ShortCircuitTarget::Value(block), ShortCircuitTarget::Value(other))
                if block.index() == 3 && other.index() == 2
        ));
    }

    #[test]
    fn collects_branch_and_block_scopes_around_close_points() {
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
            LowInstr::Close(CloseInstr { from: Reg(1) }),
            LowInstr::Jump(unluac::transformer::JumpInstr {
                target: InstrRef(4),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 0)),
            }),
        ]);

        let structure = analyze_fixture(&chunk);
        let branch_scope = structure
            .scope_candidates
            .iter()
            .find(|scope| scope.kind == ScopeKind::BranchScope)
            .expect("branch with close should produce a branch scope");
        let block_scope = structure
            .scope_candidates
            .iter()
            .find(|scope| scope.kind == ScopeKind::BlockScope)
            .expect("close block should produce a block scope");

        assert_eq!(branch_scope.entry.index(), 0);
        assert_eq!(branch_scope.exit.map(|block| block.index()), Some(2));
        assert_eq!(
            branch_scope
                .close_points
                .iter()
                .map(|instr| instr.index())
                .collect::<Vec<_>>(),
            vec![2]
        );

        assert_eq!(block_scope.entry.index(), 1);
        assert_eq!(block_scope.exit.map(|block| block.index()), Some(2));
        assert_eq!(
            block_scope
                .close_points
                .iter()
                .map(|instr| instr.index())
                .collect::<Vec<_>>(),
            vec![2]
        );
    }

    #[test]
    fn marks_irreducible_flow_with_goto_requirement() {
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
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(0))),
                    negated: false,
                },
                then_target: InstrRef(4),
                else_target: InstrRef(6),
            }),
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(3),
                value: false,
            }),
            LowInstr::Move(MoveInstr {
                dst: Reg(1),
                src: Reg(0),
            }),
            LowInstr::Jump(unluac::transformer::JumpInstr {
                target: InstrRef(2),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(1), 1)),
            }),
        ]);

        let structure = analyze_fixture(&chunk);
        let goto_requirement = structure
            .goto_requirements
            .iter()
            .find(|requirement| requirement.reason == GotoReason::IrreducibleFlow)
            .expect("irreducible flow should require a goto edge");
        let irreducible_region = structure
            .region_facts
            .iter()
            .find(|region| region.kind == RegionKind::Irreducible)
            .expect("irreducible flow should produce an irreducible region fact");

        assert!(structure.loop_candidates.is_empty());
        assert_eq!(goto_requirement.from.index(), 0);
        assert!(irreducible_region.blocks.contains(&goto_requirement.to));
        assert!(irreducible_region.blocks.len() >= 2);
    }

    #[test]
    fn prefers_while_like_when_header_is_pure_condition_and_tail_branch_exits() {
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
                then_target: InstrRef(5),
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
                then_target: InstrRef(1),
                else_target: InstrRef(4),
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(5),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let structure = analyze_fixture(&chunk);
        let candidate = structure
            .loop_candidates
            .iter()
            .find(|candidate| candidate.header.index() == 1)
            .expect("pure header loop should produce a loop candidate");

        assert_eq!(candidate.kind_hint, LoopKindHint::WhileLike);
        assert_eq!(candidate.continue_target, Some(candidate.header));
    }

    #[test]
    fn recognizes_repeat_like_when_condition_branches_into_backedge_pad() {
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
            LowInstr::Jump(JumpInstr {
                target: InstrRef(4),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Lt,
                    operands: BranchOperands::Binary(
                        unluac::transformer::CondOperand::Const(ConstRef(6)),
                        unluac::transformer::CondOperand::Reg(Reg(0)),
                    ),
                    negated: true,
                },
                then_target: InstrRef(5),
                else_target: InstrRef(6),
            }),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(2),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let structure = analyze_fixture(&chunk);
        let [candidate] = structure.loop_candidates.as_slice() else {
            panic!("repeat-like loop should produce exactly one loop candidate");
        };

        assert_eq!(candidate.kind_hint, LoopKindHint::RepeatLike);
        assert_eq!(
            candidate.continue_target.map(|block| block.index()),
            Some(2)
        );
    }
}

fn analyze_fixture(chunk: &LoweredChunk) -> unluac::structure::StructureFacts {
    let cfg = build_cfg_graph(chunk);
    let graph_facts = analyze_graph_facts(&cfg);
    let dataflow = analyze_dataflow(chunk, &cfg, &graph_facts);
    analyze_structure(chunk, &cfg, &graph_facts, &dataflow)
}

fn chunk_with_instrs(instrs: Vec<LowInstr>) -> LoweredChunk {
    LoweredChunk {
        header: ChunkHeader {
            dialect: Dialect::PucLua,
            version: DialectVersion::Lua51,
            format: 0,
            endianness: Endianness::Little,
            integer_size: 4,
            lua_integer_size: None,
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
                literals: Vec::new(),
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
