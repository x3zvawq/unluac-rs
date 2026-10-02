//! 按函数体与捕获身份一次建立两层展开调用的候选索引。
//! 重名或同形闭包不按遍历顺序任选；声明可见性仍由完整帧的词法前缀验证。

use super::*;
use crate::hir::HirProtoRef;

pub(in crate::hir::simplify::call_frames::native::expanded) struct Templates {
    pub(super) bodies: Vec<Option<Body>>,
    reads: Vec<Option<CapturedRead>>,
    pub(super) observed: Vec<Option<observed::Body>>,
    pub(super) traced: Vec<Option<crate::hir::luau_inlining::TracedReadTemplate>>,
    pub(super) checked: Vec<Option<crate::hir::luau_inlining::CheckedReadTemplate>>,
}

impl Templates {
    pub fn new(module: &HirModule, promotion: &[ProtoPromotionFacts]) -> Self {
        Self {
            checked: module
                .protos
                .iter()
                .map(|proto| anonymous::reader(proto, &promotion[proto.id.index()]))
                .collect(),
            observed: module
                .protos
                .iter()
                .map(|proto| observed::body(proto, &promotion[proto.id.index()]))
                .collect(),
            traced: module
                .protos
                .iter()
                .map(|proto| observed::reader(proto, &promotion[proto.id.index()]))
                .collect(),
            bodies: module
                .protos
                .iter()
                .map(|proto| body(proto, &promotion[proto.id.index()]))
                .collect(),
            reads: module
                .protos
                .iter()
                .map(|proto| captured_read(proto, &promotion[proto.id.index()]))
                .collect(),
        }
    }
}

#[derive(Debug, Clone)]
pub(super) struct Function {
    pub local: LocalId,
    pub child: HirProtoRef,
    pub creation: crate::hir::HirSourceSite,
    pub captures: Vec<crate::hir::HirCapture>,
}

#[derive(Debug)]
pub(super) struct Invocation {
    pub candidate: candidates::Candidate,
    pub callee: Function,
    pub reader: Function,
}

#[derive(Debug)]
pub(super) struct PairInvocation {
    pub value: HirExpr,
    pub candidate: pairs::Candidate,
    pub callee: Function,
    pub reader: Function,
}

#[derive(Debug)]
pub(super) struct NilInvocation {
    pub candidate: nil_values::Candidate,
    pub callee: Function,
    pub reader: Option<Function>,
}

pub(super) struct SharedInvocation {
    pub candidate: shared::Candidate,
    pub callee: Function,
    pub reader: Function,
}

#[derive(Default)]
pub(super) struct Invocations {
    pub values: Vec<Invocation>,
    pub pairs: Vec<PairInvocation>,
    pub nil: Vec<NilInvocation>,
    pub shared: Vec<SharedInvocation>,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ReadKey {
    bindings: [LocalId; 3],
    increment: i64,
    key: i64,
    hit: Literal,
}

fn capture(
    closure: &crate::hir::HirClosureExpr,
    id: UpvalueId,
    mode: HirCaptureMode,
) -> Option<LocalId> {
    let capture = closure.captures.get(id.index())?;
    let HirBinding::Local(local) = capture.binding else {
        return None;
    };
    (capture.mode == mode).then_some(local)
}

pub(super) fn invocations(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    templates: &Templates,
) -> Invocations {
    let mut writes = BTreeMap::new();
    visit_stmts(
        &proto.body.stmts,
        &mut BindingWriteCollector(|binding| {
            *writes.entry(binding).or_insert(0usize) += 1;
        }),
    );
    let mut functions = BTreeMap::<(Kind, Literal), Option<Function>>::new();
    let mut readers = BTreeMap::<ReadKey, Option<Function>>::new();
    let mut read_functions = BTreeMap::new();
    let mut read_keys = BTreeMap::new();
    prefix::coordinates::visit(&proto.body, &mut 0, &mut |_, kind, stmt| {
        if kind != PointKind::Statement || !matches!(stmt, HirStmt::LocalDecl(_)) {
            return;
        }
        let Some((local, HirExpr::Closure(closure))) = scalar_local(stmt) else {
            return;
        };
        let Some(creation) = closure.source_site else {
            return;
        };
        if creation.proto != proto.id
            || closure.creation.is_none()
            || writes.get(&HirBinding::Local(local)) != Some(&1)
        {
            return;
        }
        let function = Function {
            local,
            child: closure.proto,
            creation,
            captures: closure.captures.clone(),
        };
        if let Some(body) = &templates.bodies[closure.proto.index()]
            && closure.captures.is_empty()
            && let Some(fallback) = Literal::from_expr(&body.fallback)
        {
            functions
                .entry((body.kind, fallback))
                .and_modify(|value| *value = None)
                .or_insert(Some(function));
            return;
        }
        let candidate = (|| {
            let body = templates.reads[closure.proto.index()].as_ref()?;
            if closure.captures.len() != 3 {
                return None;
            }
            let bindings = [
                capture(closure, body.counter, HirCaptureMode::ByReference)?,
                capture(closure, body.index, HirCaptureMode::ByValue)?,
                capture(closure, body.table, HirCaptureMode::ByValue)?,
            ];
            if bindings[1..]
                .iter()
                .any(|local| writes.get(&HirBinding::Local(*local)) != Some(&1))
            {
                return None;
            }
            Some(ReadKey {
                bindings,
                increment: body.increment,
                key: body.key,
                hit: Literal::from_expr(&body.hit)?,
            })
        })();
        if let Some(key) = candidate {
            read_keys.insert(local, key.clone());
            read_functions.insert(local, function.clone());
            readers
                .entry(key)
                .and_modify(|value| *value = None)
                .or_insert(Some(function));
        }
    });
    if functions.is_empty() || readers.is_empty() {
        return Invocations::default();
    }
    let mut invocations = Vec::new();
    prefix::coordinates::visit(&proto.body, &mut 0, &mut |_, kind, stmt| {
        if kind != PointKind::Statement {
            return;
        }
        let HirStmt::If(branch) = stmt else {
            return;
        };
        let candidate = (|| {
            let candidate = candidates::candidate(proto, facts, branch)?;
            let callee = functions
                .get(&(Kind::Value, candidate.fallback.clone()))?
                .as_ref()?;
            let key = ReadKey {
                bindings: [candidate.counter, candidate.index, candidate.table],
                increment: candidate.increment,
                key: candidate.key,
                hit: candidate.hit.clone(),
            };
            let reader = readers.get(&key)?.as_ref()?;
            if [callee, reader]
                .iter()
                .any(|function| function.creation.instr >= candidate.source.instr)
            {
                return None;
            }
            Some(Invocation {
                candidate,
                callee: callee.clone(),
                reader: reader.clone(),
            })
        })();
        invocations.extend(candidate);
    });
    // 常量实参在原调用处已消失，只能选择唯一且可自等比较折叠的完整双返回函数。
    // 多个符合的声明没有足够身份事实，不能按遍历次序任取。
    let mut folded = functions
        .iter()
        .filter(|((kind, _), _)| *kind == Kind::Pair);
    let folded_function = folded
        .next()
        .filter(|_| folded.next().is_none())
        .and_then(|(_, function)| function.as_ref())
        .filter(|function| {
            templates.bodies[function.child.index()]
                .as_ref()
                .is_some_and(|body| {
                    crate::hir::luau_inlining::small_integer(&body.fallback).is_some()
                })
        });
    let pairs = pairs::candidates(proto, facts)
        .into_iter()
        .filter_map(|candidate| {
            let callee = if let Some(fallback) = &candidate.fallback {
                functions.get(&(Kind::Pair, fallback.clone()))?.as_ref()?
            } else {
                folded_function?
            };
            let value = if let Some(argument) = &candidate.argument {
                HirExpr::LocalRef(facts.promoted_local_for_temp(argument.source)?)
            } else {
                templates.bodies[callee.child.index()]
                    .as_ref()?
                    .fallback
                    .clone()
            };
            let key = ReadKey {
                bindings: [candidate.counter, candidate.index, candidate.table],
                increment: candidate.increment,
                key: candidate.key,
                hit: candidate.hit.clone(),
            };
            let reader = readers.get(&key)?.as_ref()?;
            if [callee, reader]
                .iter()
                .any(|function| function.creation.instr >= candidate.source.instr)
            {
                return None;
            }
            Some(PairInvocation {
                value,
                candidate,
                callee: callee.clone(),
                reader: reader.clone(),
            })
        })
        .collect();
    let mut nil_functions = functions
        .iter()
        .filter(|((kind, _), _)| *kind == Kind::Value);
    let nil_function = nil_functions
        .next()
        .filter(|_| nil_functions.next().is_none())
        .and_then(|(_, function)| function.as_ref());
    let mut views = BTreeMap::new();
    for (view, value) in facts.readonly_debug_views() {
        views
            .entry((view.start_pc, view.end, view.name.as_str()))
            .and_modify(|entry| *entry = None)
            .or_insert(Some(value));
    }
    let nil = nil_values::candidates(proto, facts)
        .into_iter()
        .filter_map(|candidate| {
            let callee = nil_function?;
            let body = templates.bodies[callee.child.index()].as_ref()?;
            let reader = if let Some(name) = body.names[2].as_deref() {
                match views.get(&(candidate.source_pc, candidate.end, name)) {
                    None => None,
                    Some(Some(Some(value))) => {
                        let reader = read_functions.get(&facts.promoted_local_for_temp(*value)?)?;
                        if facts.operation_result_temp(reader.creation) != Some(*value) {
                            return None;
                        }
                        Some(reader)
                    }
                    // 候选拒绝[ProofIncomplete:DebugView]：原视图存在但身份未获证明，
                    // 不能当作 stripped，也不能按同形闭包的数量挑选实参。
                    _ => return None,
                }
            } else {
                None
            };
            if std::iter::once(callee)
                .chain(reader)
                .any(|function| function.creation.instr >= candidate.source.instr)
            {
                return None;
            }
            Some(NilInvocation {
                candidate,
                callee: callee.clone(),
                reader: reader.cloned(),
            })
        })
        .collect();
    let mut shared_functions = functions
        .iter()
        .filter(|((kind, _), _)| *kind == Kind::Shared);
    let shared_function = shared_functions
        .next()
        .filter(|_| shared_functions.next().is_none())
        .and_then(|(_, function)| function.as_ref());
    let shared = shared::candidates(proto, facts)
        .into_iter()
        .filter_map(|candidate| {
            let callee = shared_function?;
            let body = templates.bodies[callee.child.index()].as_ref()?;
            if candidate.live.as_ref().is_some_and(|value| {
                body.selection_hit.as_ref() != Some(&value.hit)
                    || Literal::from_expr(&body.fallback).as_ref() != Some(&value.fallback)
            }) {
                return None;
            }
            let key = ReadKey {
                bindings: [
                    candidate.read.counter,
                    candidate.read.index,
                    candidate.read.table,
                ],
                increment: candidate.read.increment,
                key: candidate.read.key,
                hit: candidate.read.hit.clone(),
            };
            let end = candidate.end;
            let view = body.names[2]
                .as_deref()
                .and_then(|name| views.get(&(candidate.argument.body_pc, end, name)));
            let reader = match view {
                None => readers.get(&key)?.as_ref()?,
                Some(Some(Some(value))) => {
                    let local = facts.promoted_local_for_temp(*value)?;
                    let reader = read_functions.get(&local)?;
                    if read_keys.get(&local) != Some(&key)
                        || facts.operation_result_temp(reader.creation) != Some(*value)
                    {
                        return None;
                    }
                    reader
                }
                // 候选拒绝[ProofIncomplete:DebugView]：执行效果相同也不能覆盖未证明的原参数身份。
                _ => return None,
            };
            if [callee, reader]
                .iter()
                .any(|function| function.creation.instr >= candidate.source.instr)
            {
                return None;
            }
            Some(SharedInvocation {
                candidate,
                callee: callee.clone(),
                reader: reader.clone(),
            })
        })
        .collect();
    Invocations {
        values: invocations,
        pairs,
        nil,
        shared,
    }
}
