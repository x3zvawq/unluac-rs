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
    BranchKind, GotoReason, LoopKindHint, RegionKind, ScopeKind, ShortCircuitKindHint,
    analyze_structure,
};
use unluac::transformer::{
    BranchCond, BranchInstr, BranchOperands, BranchPredicate, CloseInstr, InstrRef, LoadBoolInstr,
    LowInstr, LoweredChunk, LoweredProto, LoweringMap, MoveInstr, Reg, RegRange, ReturnInstr,
    ValuePack,
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
            .find(|candidate| candidate.header.index() == 0)
            .expect("or-like lowering should produce a short-circuit candidate");

        assert_eq!(candidate.merge.index(), 2);
        assert_eq!(candidate.result_reg, Some(Reg(0)));
        assert_eq!(candidate.kind_hint, ShortCircuitKindHint::OrLike);
        assert!(candidate.reducible);
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
