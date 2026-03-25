//! 这些测试固定共享分析层的层内契约。
//!
//! 它们直接手工构造 low-IR，而不是经过 parser/transformer，是为了让失败点
//! 只指向 CFG / GraphFacts / Dataflow 自己的规则实现。

use unluac::cfg::{
    EdgeKind, PhiId, SsaValue, analyze_dataflow, analyze_graph_facts, build_cfg_graph,
};
use unluac::parser::{
    ChunkHeader, Dialect, DialectConstPoolExtra, DialectDebugExtra, DialectHeaderExtra,
    DialectUpvalueExtra, DialectVersion, Endianness, Lua51ConstPoolExtra, Lua51DebugExtra,
    Lua51HeaderExtra, Lua51UpvalueExtra, Origin, ProtoFrameInfo, ProtoLineRange, ProtoSignature,
    RawConstPool, RawConstPoolCommon, RawDebugInfo, RawDebugInfoCommon, RawUpvalueInfo,
    RawUpvalueInfoCommon, Span,
};
use unluac::transformer::{
    BranchCond, BranchInstr, BranchOperands, BranchPredicate, InstrRef, LoadBoolInstr,
    LoadConstInstr, LowInstr, LoweredChunk, LoweredProto, LoweringMap, MoveInstr, Reg, RegRange,
    ResultPack, ReturnInstr, ValuePack, VarArgInstr,
};

mod build_cfg_graph_shared {
    use super::*;

    #[test]
    fn builds_loop_blocks_and_edges_for_shared_low_ir() {
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
                values: ValuePack::Fixed(RegRange::new(Reg(0), 1)),
            }),
        ]);

        let graph = build_cfg_graph(&chunk);
        let cfg = &graph.cfg;
        let facts = analyze_graph_facts(&graph);

        assert_eq!(cfg.block_order.len(), 4);
        assert_eq!(
            cfg.edges
                .iter()
                .map(|edge| (edge.from.index(), edge.to.index(), edge.kind))
                .collect::<Vec<_>>(),
            vec![
                (0, 1, EdgeKind::Fallthrough),
                (1, 2, EdgeKind::BranchTrue),
                (1, 3, EdgeKind::BranchFalse),
                (2, 1, EdgeKind::Jump),
                (3, 4, EdgeKind::Return),
            ]
        );
        assert_eq!(
            cfg.reachable_blocks
                .iter()
                .map(|block| block.index())
                .collect::<Vec<_>>(),
            vec![0, 1, 2, 3, 4]
        );
        assert_eq!(
            facts
                .backedges
                .iter()
                .map(|edge| edge.index())
                .collect::<Vec<_>>(),
            vec![3]
        );
        assert_eq!(
            facts
                .loop_headers
                .iter()
                .map(|block| block.index())
                .collect::<Vec<_>>(),
            vec![1]
        );
        assert_eq!(
            facts.natural_loops[0]
                .blocks
                .iter()
                .map(|block| block.index())
                .collect::<Vec<_>>(),
            vec![1, 2]
        );
    }
}

mod analyze_dataflow_shared {
    use super::*;

    #[test]
    fn builds_phi_candidates_and_use_defs_at_diamond_join() {
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
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(1),
                value: unluac::transformer::ConstRef(0),
            }),
            LowInstr::Jump(unluac::transformer::JumpInstr {
                target: InstrRef(5),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(1),
                value: unluac::transformer::ConstRef(1),
            }),
            LowInstr::Move(MoveInstr {
                dst: Reg(2),
                src: Reg(1),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(2), 1)),
            }),
        ]);

        let cfg = build_cfg_graph(&chunk);
        let graph_facts = analyze_graph_facts(&cfg);
        let dataflow = analyze_dataflow(&chunk, &cfg, &graph_facts);

        assert_eq!(dataflow.defs.len(), 4);
        assert_eq!(dataflow.phi_candidates.len(), 1);

        let phi = &dataflow.phi_candidates[0];
        assert_eq!(phi.block.index(), 3);
        assert_eq!(phi.reg, Reg(1));
        assert_eq!(
            phi.incoming
                .iter()
                .map(|incoming| {
                    (
                        incoming.pred.index(),
                        incoming
                            .defs
                            .iter()
                            .map(|def| def.index())
                            .collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>(),
            vec![(1, vec![1]), (2, vec![2])]
        );

        let reaching = &dataflow.reaching_defs[5].fixed[&Reg(1)];
        assert_eq!(
            reaching.iter().map(|def| def.index()).collect::<Vec<_>>(),
            vec![1, 2]
        );
        let use_defs = &dataflow.use_defs[5].fixed[&Reg(1)];
        assert_eq!(
            use_defs.iter().map(|def| def.index()).collect::<Vec<_>>(),
            vec![1, 2]
        );
        let reaching_values = &dataflow.reaching_values[5].fixed[&Reg(1)];
        assert_eq!(
            reaching_values.iter().copied().collect::<Vec<_>>(),
            vec![SsaValue::Phi(PhiId(0))]
        );
        let use_values = &dataflow.use_values[5].fixed[&Reg(1)];
        assert_eq!(
            use_values.iter().copied().collect::<Vec<_>>(),
            vec![SsaValue::Phi(PhiId(0))]
        );
        assert_eq!(
            dataflow.live_in[3]
                .iter()
                .map(|reg| reg.index())
                .collect::<Vec<_>>(),
            vec![1]
        );
    }

    #[test]
    fn tracks_open_pack_defs_and_uses_in_separate_channel() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::VarArg(VarArgInstr {
                results: ResultPack::Open(Reg(1)),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Open(Reg(1)),
            }),
        ]);

        let cfg = build_cfg_graph(&chunk);
        let graph_facts = analyze_graph_facts(&cfg);
        let dataflow = analyze_dataflow(&chunk, &cfg, &graph_facts);

        assert_eq!(dataflow.open_defs.len(), 1);
        assert_eq!(
            dataflow.open_reaching_defs[1]
                .iter()
                .map(|open_def| open_def.index())
                .collect::<Vec<_>>(),
            vec![0]
        );
        assert_eq!(
            dataflow.open_use_defs[1]
                .iter()
                .map(|open_def| open_def.index())
                .collect::<Vec<_>>(),
            vec![0]
        );
        assert_eq!(dataflow.open_def_uses[0].len(), 1);
        assert_eq!(dataflow.open_def_uses[0][0].instr.index(), 1);
    }

    #[test]
    fn treats_open_pack_fixed_prefix_as_real_fixed_uses() {
        let chunk = chunk_with_instrs(vec![
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(0),
                value: unluac::transformer::ConstRef(0),
            }),
            LowInstr::GetTable(unluac::transformer::GetTableInstr {
                dst: Reg(1),
                base: unluac::transformer::AccessBase::Env,
                key: unluac::transformer::AccessKey::Const(unluac::transformer::ConstRef(1)),
            }),
            LowInstr::Call(unluac::transformer::CallInstr {
                callee: Reg(1),
                args: ValuePack::Fixed(RegRange::new(Reg(2), 0)),
                results: ResultPack::Open(Reg(1)),
                kind: unluac::transformer::CallKind::Normal,
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Open(Reg(0)),
            }),
        ]);

        let cfg = build_cfg_graph(&chunk);
        let graph_facts = analyze_graph_facts(&cfg);
        let dataflow = analyze_dataflow(&chunk, &cfg, &graph_facts);

        assert_eq!(
            dataflow.use_defs[3]
                .fixed
                .get(Reg(0))
                .expect("open pack prefix should count as fixed use")
                .iter()
                .copied()
                .collect::<Vec<_>>(),
            vec![dataflow.instr_defs[0][0]]
        );
        assert_eq!(
            dataflow.use_values[3]
                .fixed
                .get(Reg(0))
                .expect("open pack prefix should count as fixed value use")
                .iter()
                .copied()
                .collect::<Vec<_>>(),
            vec![SsaValue::Def(dataflow.instr_defs[0][0])]
        );
        assert_eq!(
            dataflow.open_use_defs[3]
                .iter()
                .map(|open_def| open_def.index())
                .collect::<Vec<_>>(),
            vec![0]
        );
    }

    #[test]
    fn keeps_multiple_reaching_defs_per_phi_incoming_edge() {
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
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(1),
                value: unluac::transformer::ConstRef(0),
            }),
            LowInstr::Jump(unluac::transformer::JumpInstr {
                target: InstrRef(6),
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(1),
                value: unluac::transformer::ConstRef(1),
            }),
            LowInstr::Jump(unluac::transformer::JumpInstr {
                target: InstrRef(6),
            }),
            LowInstr::Branch(BranchInstr {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(unluac::transformer::CondOperand::Reg(Reg(0))),
                    negated: false,
                },
                then_target: InstrRef(8),
                else_target: InstrRef(10),
            }),
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(3),
                value: false,
            }),
            LowInstr::LoadConst(LoadConstInstr {
                dst: Reg(1),
                value: unluac::transformer::ConstRef(2),
            }),
            LowInstr::Jump(unluac::transformer::JumpInstr {
                target: InstrRef(10),
            }),
            LowInstr::Move(MoveInstr {
                dst: Reg(4),
                src: Reg(1),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(4), 1)),
            }),
        ]);

        let cfg = build_cfg_graph(&chunk);
        let graph_facts = analyze_graph_facts(&cfg);
        let dataflow = analyze_dataflow(&chunk, &cfg, &graph_facts);

        let phi = dataflow
            .phi_candidates
            .iter()
            .find(|candidate| {
                candidate.reg == Reg(1)
                    && candidate
                        .incoming
                        .iter()
                        .any(|incoming| incoming.defs.len() > 1)
            })
            .expect("outer merge should produce a phi candidate for r1");

        assert_eq!(
            phi.incoming
                .iter()
                .map(|incoming| {
                    (
                        incoming.pred.index(),
                        incoming
                            .defs
                            .iter()
                            .map(|def| def.index())
                            .collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>(),
            vec![(3, vec![1, 2]), (5, vec![4])]
        );
    }
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
