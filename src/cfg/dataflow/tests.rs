use std::collections::BTreeSet;

use super::*;

#[test]
fn tracked_state_snapshot_preserves_sparse_contents() {
    let mut state = TrackedState::new(8);
    state.set_singleton(Reg(4), DefId(11));
    state.insert(Reg(4), DefId(12));
    state.set_singleton(Reg(1), DefId(3));

    let snapshot = state.snapshot_map();

    assert_eq!(snapshot.keys().collect::<Vec<_>>(), vec![Reg(1), Reg(4)]);
    assert_eq!(
        snapshot.get(Reg(1)).cloned(),
        Some(CompactSet::singleton(DefId(3)))
    );
    assert_eq!(
        snapshot.get(Reg(4)).cloned(),
        Some(CompactSet::Many(BTreeSet::from([DefId(11), DefId(12)])))
    );
    assert_eq!(snapshot.get(Reg(7)), None);
}

#[test]
fn resolved_fixed_use_regs_should_include_open_gap_prefix() {
    let mut effect = InstrEffect::default();
    effect.fixed_uses.extend([Reg(1), Reg(5)]);
    effect.open_use = Some(Reg(2));

    let open_defs = vec![OpenDef {
        id: OpenDefId(0),
        start_reg: Reg(4),
        instr: crate::transformer::InstrRef(0),
        block: BlockRef(0),
    }];
    let current_open = CompactSet::singleton(OpenDefId(0));
    let mut scratch = MaterializeScratch::new(8);

    let regs = scratch
        .fixed_use_regs
        .resolve(&effect, &current_open, &open_defs);

    assert_eq!(regs, &[Reg(1), Reg(2), Reg(3), Reg(5)]);
}

#[test]
fn block_phi_values_should_override_reaching_defs_in_snapshot() {
    let mut state = ValueState::new(4);
    state.set_singleton(Reg(1), SsaValue::Def(DefId(7)));

    values::apply_block_phi_values(
        &mut state,
        &[PhiCandidate {
            id: PhiId(2),
            block: BlockRef(1),
            reg: Reg(1),
            incoming: Vec::new(),
        }],
    );

    let snapshot = state.snapshot_map();

    assert_eq!(
        snapshot.get(Reg(1)).cloned(),
        Some(CompactSet::singleton(SsaValue::Phi(PhiId(2))))
    );
}

#[test]
fn no_phi_value_queries_should_wrap_defs_as_ssa_defs() {
    let reaching_defs = InstrReachingDefs {
        fixed: RegValueMap::from_sparse_entries(vec![
            (Reg(0), CompactSet::singleton(DefId(1))),
            (
                Reg(2),
                CompactSet::Many(BTreeSet::from([DefId(3), DefId(4)])),
            ),
        ]),
    };
    let use_defs = InstrUseDefs {
        fixed: RegValueMap::from_sparse_entries(vec![(
            Reg(2),
            CompactSet::singleton(DefId(4)),
        )]),
        open: BTreeSet::new(),
    };
    let dataflow = DataflowFacts {
        instr_effects: vec![InstrEffect::default()],
        effect_summaries: vec![SideEffectSummary::default()],
        defs: Vec::new(),
        open_defs: Vec::new(),
        instr_defs: vec![Vec::new()],
        reaching_defs: vec![reaching_defs],
        use_defs: vec![use_defs],
        def_uses: Vec::new(),
        open_reaching_defs: vec![BTreeSet::new()],
        open_use_defs: vec![BTreeSet::new()],
        open_def_uses: Vec::new(),
        live_in: Vec::new(),
        live_out: Vec::new(),
        open_live_in: Vec::new(),
        open_live_out: Vec::new(),
        phi_candidates: Vec::new(),
        phi_block_ranges: Vec::new(),
        value_facts: ValueFactsStorage::NoPhi,
        children: Vec::new(),
    };

    assert_eq!(
        dataflow
            .reaching_values_at(crate::transformer::InstrRef(0))
            .get(Reg(0))
            .map(|values| values.to_compact_set()),
        Some(CompactSet::singleton(SsaValue::Def(DefId(1))))
    );
    assert_eq!(
        dataflow
            .reaching_values_at(crate::transformer::InstrRef(0))
            .get(Reg(2))
            .map(|values| values.to_compact_set()),
        Some(CompactSet::Many(BTreeSet::from([
            SsaValue::Def(DefId(3)),
            SsaValue::Def(DefId(4)),
        ])))
    );
    assert_eq!(
        dataflow
            .use_values_at(crate::transformer::InstrRef(0))
            .get(Reg(2))
            .map(|values| values.to_compact_set()),
        Some(CompactSet::singleton(SsaValue::Def(DefId(4))))
    );
}
