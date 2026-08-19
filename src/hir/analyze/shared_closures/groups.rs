//! 收集可复用 shared-closure 组与 owner template 入口；依赖 lowered closure identity，不负责递归模板匹配；例如拒绝同 shared id 指向不同 child proto。

use super::*;

pub(super) const fn origin_key(origin: Origin) -> (usize, usize, Option<u64>) {
    (origin.span.offset, origin.span.size, origin.raw_word)
}

#[derive(Debug)]
pub(super) struct ReusableGroup {
    pub(super) shared: SharedClosureRef,
    pub(super) proto: ProtoRef,
    pub(super) instrs: Vec<InstrRef>,
    pub(super) has_captures: bool,
    pub(super) consistent_proto: bool,
}

impl ReusableGroup {
    pub(super) fn error(&self) -> HirLowerError {
        HirLowerError::UnrepresentableRepeatedCapturedSharedClosure {
            shared_index: self.shared.0,
            instr: self.instrs.first().map_or(0, |instr| instr.index()),
        }
    }
}

pub(super) fn collect_reusable_groups(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
) -> BTreeMap<SharedClosureRef, ReusableGroup> {
    let mut groups = BTreeMap::new();
    for (index, instr) in proto.instrs.iter().enumerate() {
        let instr_ref = InstrRef(index);
        if !instr_is_reachable(cfg, instr_ref) {
            continue;
        }
        let LowInstr::Closure(closure) = instr else {
            continue;
        };
        let ClosureCreation::Reusable(shared) = closure.creation else {
            continue;
        };
        if dataflow.instr_def_for_reg(instr_ref, closure.dst).is_none() {
            continue;
        }
        let group = groups.entry(shared).or_insert_with(|| ReusableGroup {
            shared,
            proto: closure.proto,
            instrs: Vec::new(),
            has_captures: false,
            consistent_proto: true,
        });
        group.consistent_proto &= group.proto == closure.proto;
        group.instrs.push(instr_ref);
        group.has_captures |= !closure.captures.is_empty();
    }
    groups
}

#[derive(Debug)]
pub(super) struct OwnerTemplate {
    pub(super) instr: InstrRef,
    pub(super) template: Arc<ClosureTemplate>,
}

pub(super) fn collect_owner_templates(
    proto: &LoweredProto,
    cfg_graph: &CfgGraph,
    dataflow: &DataflowFacts,
) -> Vec<OwnerTemplate> {
    let mut templates = BTreeMap::<_, Option<Arc<ClosureTemplate>>>::new();
    let mut owners = Vec::new();
    for (index, instr) in proto.instrs.iter().enumerate() {
        let instr_ref = InstrRef(index);
        if !instr_is_reachable(&cfg_graph.cfg, instr_ref) {
            continue;
        }
        let LowInstr::Closure(closure) = instr else {
            continue;
        };
        let Some(child) = proto.children.get(closure.proto.index()) else {
            continue;
        };
        let template = templates
            .entry(origin_key(child.origin))
            .or_insert_with(|| {
                let child_cfg = cfg_graph.children.get(closure.proto.index())?;
                let child_dataflow = dataflow.children.get(closure.proto.index())?;
                extract_template(child, &child_cfg.cfg, child_dataflow).map(Arc::new)
            })
            .clone();
        if let Some(template) = template {
            owners.push(OwnerTemplate {
                instr: instr_ref,
                template,
            });
        }
    }
    owners
}
