//! 这个文件负责清理已经没有源码意义的机械 AST 壳。
//!
//! 它依赖前面的结构恢复和 readability pass 已经把真正需要保留的局部作用域、
//! 控制流和显式 return 暴露出来；这里专门删除“只剩形式意义”的 do-end、空 local、
//! 以及 chunk/function 结尾的无值 return。尾部 do-end 的作用域证明显式区分普通
//! block 出口和 repeat 的 `until` 条件：前者与父 block 同时退出，后者仍会在父域中
//! 求值。它不会越权合并业务语句，也不会把仍有词法意义的块错误拍平。
//!
//! 例子：
//! - `do print(x) end` 会在内部没有局部作用域意义时折成 `print(x)`
//! - `local t0` 这种只剩机械 temp 壳、且没有值也没有使用的声明会被删除
//! - 未使用的 recovered `local t0 = side_effect()` 会保留为 `side_effect()` 调用
//! - 函数尾部的 `return` 会在没有返回值时被去掉

use std::collections::{BTreeMap, BTreeSet};

use super::super::common::{
    AstBindingRef, AstBlock, AstCallKind, AstCallStmt, AstExpr, AstFunctionName, AstLValue,
    AstLocalAttr, AstLocalDecl, AstLocalOrigin, AstModule, AstStmt,
};
use super::ReadabilityContext;
use super::binding_flow::{BindingUseIndex, binding_mentions_in_expr, binding_mentions_in_stmt};
use super::expr_analysis::is_discard_safe_expr;
use super::walk::{self, AstRewritePass, BlockKind};
use crate::ast::traverse::traverse_expr_children;

pub(super) fn apply(module: &mut AstModule, _context: ReadabilityContext) -> bool {
    walk::rewrite_module(module, &mut CleanupPass)
}

struct CleanupPass;

impl AstRewritePass for CleanupPass {
    fn rewrite_block(&mut self, block: &mut AstBlock, kind: BlockKind) -> bool {
        cleanup_block(
            block,
            matches!(kind, BlockKind::ModuleBody | BlockKind::FunctionBody),
            None,
        )
    }

    fn rewrite_repeat_body(&mut self, block: &mut AstBlock, condition: &AstExpr) -> bool {
        cleanup_block(block, false, Some(condition))
    }
}

fn cleanup_block(
    block: &mut AstBlock,
    allow_trailing_empty_return_elision: bool,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let mut changed = false;

    let old_stmts = std::mem::take(&mut block.stmts);
    let mut flattened_stmts = Vec::with_capacity(old_stmts.len());
    for stmt in old_stmts {
        match stmt {
            AstStmt::DoBlock(nested)
                if nested.stmts.len() == 1 && can_elide_single_stmt_do_block(&nested.stmts[0]) =>
            {
                // 这里专门清理“只剩一条非局部作用域语句”的机械 do-end。
                // 它通常是前层为了暂存中间 local 范围而留下来的壳；一旦内部局部已经被
                // 其他 pass 收回，这层壳继续保留只会让源码多出无意义缩进。
                flattened_stmts.extend(nested.stmts);
                changed = true;
            }
            other => flattened_stmts.push(other),
        }
    }
    block.stmts = flattened_stmts;

    // A recovered call result can be an implementation-only value that is immediately
    // overwritten before any read. Keep the call at its original evaluation point, but
    // declare the binding with the value that actually survives. This removes a misleading
    // `local x = f(); x = value` pair without moving a call across another statement.
    changed |= split_overwritten_call_result_locals(block);

    // 尾部 do-end 展开：当 do-end 是块的最后一条语句时，其内部 local 的作用域
    // 在父块结束处同样终止，do-end 仅是多余的缩进壳。
    // 典型来源：guard-flip 把 `if cond then BODY else return end` 拉平成
    // `if not cond then return end; do BODY end`，其中 BODY 含 local 声明。
    // repeat body 与 until 条件共享外层作用域；只有这种尾条件存在时，global、`<close>`
    // local 和局部 closure 才需要额外边界。普通 block 的尾 do 与父 block 同时退出，
    // 因而可安全去掉缩进壳（regress344 覆盖函数尾 `<close>` + return）。
    while let Some(AstStmt::DoBlock(nested)) = block.stmts.last()
        && trailing_do_block_is_scope_neutral(nested, trailing_condition.is_some())
    {
        let Some(AstStmt::DoBlock(nested)) = block.stmts.pop() else {
            unreachable!();
        };
        block.stmts.extend(nested.stmts);
        changed = true;
    }

    let binding_flow = BlockBindingFlow::new(block, trailing_condition);
    changed |= trim_unused_initialized_local_suffix(block, &binding_flow);
    let original_stmts = std::mem::take(&mut block.stmts);
    let mut retained_stmts = Vec::with_capacity(original_stmts.len());
    for stmt in original_stmts {
        match stmt {
            // 候选拒绝[SemanticBarrier:ValueArity]：多目标声明只允许上面的 helper 删除连续
            // 尾槽。删除未使用前缀/中间槽会移动后续 binding 对应的返回值，例如
            // `local dead, keep = pair()` 会让 keep 从第二返回值错取第一返回值。
            // 候选拒绝[SemanticBarrier:Lifetime]：有 initializer 的 `<close>` 即使无普通 use
            // 也必须在域末执行 `__close`（regress246）。`<const>` 没有退出动作，在其 binding
            // 无引用且 initializer 可安全丢弃/保留为 call 时允许清理。
            // 候选拒绝[PolicyBoundary]：DebugHinted 身份保留；候选拒绝[SemanticBarrier:Lifetime]：
            // PhysicalRoot 可能由弱表/`__gc` 观察，不能按普通未使用 local 删除。
            // 候选拒绝[SemanticBarrier:Scope]：声明外仍有读取、capture 或写入时，删除 local
            // 会改变读取值、捕获 cell，或让后续 name target 解析成外层/global。
            AstStmt::LocalDecl(mut local_decl)
                if local_decl.bindings.len() == 1
                    && local_decl.values.len() == 1
                    && local_decl.bindings[0].attr != AstLocalAttr::Close
                    && local_decl.bindings[0].origin == AstLocalOrigin::Recovered
                    && !binding_flow.keeps_decl_alive(local_decl.bindings[0].id) =>
            {
                if is_discard_safe_expr(&local_decl.values[0]) {
                    // 候选接受：表达式无求值副作用，且 binding-flow 已证明域内外均无读取、
                    // capture 或写入；删除声明不会移除可观察求值或词法槽。
                    changed = true;
                } else {
                    let Some(value) = local_decl.values.pop() else {
                        retained_stmts.push(AstStmt::LocalDecl(local_decl));
                        continue;
                    };
                    match into_call_kind(value) {
                        Ok(call) => {
                            // 候选接受：call 仍在原语句位置执行一次，仅丢弃未使用的结果。
                            retained_stmts.push(AstStmt::CallStmt(Box::new(AstCallStmt { call })));
                            changed = true;
                        }
                        Err(value) => {
                            // 候选拒绝[SemanticBarrier:EvalCount]：如 `local _ = obj[key]` 的
                            // 查表可能触发 `__index`；删除会少求值一次且 Lua 无通用表达式
                            // 语句承载它，regress178 的 unused global read 直接统计该观察量。
                            local_decl.values.push(value);
                            retained_stmts.push(AstStmt::LocalDecl(local_decl));
                        }
                    }
                }
            }
            other => retained_stmts.push(other),
        }
    }
    block.stmts = retained_stmts;

    let binding_flow = BlockBindingFlow::new(block, trailing_condition);
    let live_empty_bindings = collect_live_empty_bindings(block, &binding_flow);
    for stmt in &mut block.stmts {
        let AstStmt::LocalDecl(local_decl) = stmt else {
            continue;
        };
        if !local_decl.values.is_empty() {
            continue;
        }
        let original_len = local_decl.bindings.len();
        local_decl.bindings.retain(|binding| {
            if binding.origin == AstLocalOrigin::DebugHinted {
                // 候选拒绝[PolicyBoundary]：DebugHinted 空声明仍是显式源码身份。
                return true;
            }

            let is_live = live_empty_bindings.contains(&binding.id);
            if is_live {
                // 候选拒绝[SemanticBarrier:Scope]：仍有读取、capture 或写入的 recovered
                // binding 必须保留，否则引用会失去原词法槽或写到外层名字。
            } else {
                // 候选接受：空 declaration 只把 binding 初始化为 nil；即使带 `<close>` 或
                // PhysicalRoot provenance，也没有对象 root/关闭动作。binding-flow 又证明它
                // 没有域内外引用，因此删除不改变求值、生命周期或名字解析。
            }
            is_live
        });
        changed |= local_decl.bindings.len() != original_len;
    }

    let original_len = block.stmts.len();
    // 候选接受：前一步只会产生 binding/value 同为空的声明壳；删除空 stmt 不再改变
    // initializer 求值或任何 binding 的作用域。
    block.stmts.retain(|stmt| match stmt {
        AstStmt::LocalDecl(local_decl) => {
            !(local_decl.bindings.is_empty() && local_decl.values.is_empty())
        }
        _ => true,
    });
    changed |= block.stmts.len() != original_len;

    if allow_trailing_empty_return_elision
        && matches!(
            block.stmts.last(),
            Some(AstStmt::Return(ret)) if ret.values.is_empty()
        )
    {
        // 候选接受：仅限 chunk/function 顶层 block 的最后一条无值 return；自然落出返回
        // 同样的零个结果，且不存在后继语句或 repeat 尾条件。
        block.stmts.pop();
        changed = true;
    }

    changed
}

fn trim_unused_initialized_local_suffix(
    block: &mut AstBlock,
    binding_flow: &BlockBindingFlow,
) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        let AstStmt::LocalDecl(local_decl) = stmt else {
            continue;
        };
        if local_decl.bindings.len() <= 1 || local_decl.values.is_empty() {
            continue;
        }

        let retained_len = local_decl
            .bindings
            .iter()
            .rposition(|binding| {
                binding.attr == AstLocalAttr::Close
                    || binding.origin != AstLocalOrigin::Recovered
                    || binding_flow.keeps_decl_alive(binding.id)
            })
            .map_or(1, |index| index + 1);
        if retained_len < local_decl.bindings.len() {
            // 候选接受：只删除逐 binding 证明无 use/capture/write 的连续尾槽；RHS
            // 完整保留，因此既不改变求值，也不移动任何保留 binding 的返回值位置。
            // 全部尾槽都满足时仍留一个，交由既有单槽事务按 initializer 类型处理。
            local_decl.bindings.truncate(retained_len);
            changed = true;
        }
    }
    changed
}

fn split_overwritten_call_result_locals(block: &mut AstBlock) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let mut rewritten = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    let mut index = 0;

    while index < old_stmts.len() {
        if let Some((call, declaration)) =
            old_stmts.get(index).zip(old_stmts.get(index + 1)).and_then(
                |(declaration, overwrite)| split_overwritten_call_result(declaration, overwrite),
            )
        {
            rewritten.push(AstStmt::CallStmt(Box::new(AstCallStmt { call })));
            rewritten.push(AstStmt::LocalDecl(Box::new(declaration)));
            index += 2;
            changed = true;
        } else {
            rewritten.push(
                old_stmts
                    .get(index)
                    .cloned()
                    .expect("cleanup scan index must stay in bounds"),
            );
            index += 1;
        }
    }

    block.stmts = rewritten;
    changed
}

fn split_overwritten_call_result(
    declaration: &AstStmt,
    overwrite: &AstStmt,
) -> Option<(AstCallKind, AstLocalDecl)> {
    let AstStmt::LocalDecl(local_decl) = declaration else {
        // 候选忽略[NotApplicable]：pair 首句不是 local declaration。
        return None;
    };
    let AstStmt::Assign(assign) = overwrite else {
        // 候选忽略[NotApplicable]：相邻后继不是 overwrite assignment。
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        // 分析停用[ProofIncomplete]：多 binding declaration 需要 value-pack 到槽的逐项对应；
        // 空 declaration 不产生 call-result 候选。
        return None;
    };
    let [call_value] = local_decl.values.as_slice() else {
        // 分析停用[ProofIncomplete]：多 value declaration 需要 Lua 尾值展开事实；空 value
        // declaration 不产生 call-result 候选。
        return None;
    };
    match binding.attr {
        AstLocalAttr::None => {}
        AstLocalAttr::Close => {
            // 候选拒绝[SemanticBarrier:Lifetime]：`<close>` 的退出动作不可从 call result
            // 移到 replacement；regress246 证明 `__close` 时点可由后继 condition 观察。
            return None;
        }
        AstLocalAttr::Const => {
            // 候选拒绝[TargetConstraint]：`<const>` binding 不允许后继 overwrite；这种 pair
            // 不是可生成的合法 Lua 源码形状，cleanup 不把它改写成另一种声明。
            return None;
        }
    }
    match binding.origin {
        AstLocalOrigin::Recovered => {}
        AstLocalOrigin::PhysicalRoot => {
            // 候选拒绝[SemanticBarrier:Lifetime]：PhysicalRoot call result 必须活到 overwrite
            // RHS 完成；lua54_01_close#17 用 `__gc` 观察同槽 clear 前的旧值仍存活。
            return None;
        }
        AstLocalOrigin::DebugHinted => {
            // 候选拒绝[PolicyBoundary]：DebugHinted initializer 是项目选择保留的源码声明身份。
            return None;
        }
    }
    let [target] = assign.targets.as_slice() else {
        // 分析停用[ProofIncomplete]：并行赋值需要全部 target/RHS 的快照与覆盖关系。
        return None;
    };
    if assign.values.is_empty() {
        // 候选忽略[NotApplicable]：空 RHS 不产生可转入 local declaration 的 replacement。
        return None;
    }
    if !matches!(target, super::super::common::AstLValue::Name(name) if binding.id.matches_name_ref(name))
    {
        // 候选忽略[NotApplicable]：后继没有直接覆盖所声明的同一 binding。
        return None;
    }
    if assign
        .values
        .iter()
        .any(|value| binding_mentions_in_expr(value).contains(&binding.id))
    {
        // 候选拒绝[SemanticBarrier:Scope]：`local x=f(); x=1,use(x)` 改成
        // `f(); local x=1,use(x)` 后 RHS 的 `x` 会解析到外层而非 call result。
        return None;
    }

    let call = match into_call_kind(call_value.clone()) {
        Ok(call) => call,
        Err(_) => {
            // 候选忽略[NotApplicable]：initializer 不是可独立保留的 call statement。
            return None;
        }
    };

    // 候选接受：call 与单目标 overwrite 相邻；binding 是无属性 recovered local，且所有
    // overwrite RHS 都不读取它。call 在原 initializer 和改写后的独立语句中都位于 binding
    // 的词法起点之前，即使表达式异常地标成同一 ID，名字解析环境也不变。完整 RHS 列表
    // 原样转入单 binding local declaration，Lua 的求值顺序、值宽度和最终 binding 值保持不变。
    Some((
        call,
        AstLocalDecl {
            bindings: local_decl.bindings.clone(),
            values: assign.values.clone(),
        },
    ))
}

fn trailing_do_block_is_scope_neutral(block: &AstBlock, has_trailing_condition: bool) -> bool {
    if !has_trailing_condition {
        // 候选接受：尾 do 与普通父 block 在同一控制流出口结束；展开不会移动任何后继
        // 求值，local/`<close>`/closure 的退出时点仍是该出口（regress344）。
        return true;
    }

    let scoped_bindings = block
        .stmts
        .iter()
        .flat_map(|stmt| match stmt {
            AstStmt::LocalDecl(local_decl) => local_decl
                .bindings
                .iter()
                .map(|binding| binding.id)
                .collect::<Vec<_>>(),
            AstStmt::LocalFunctionDecl(function_decl) => vec![function_decl.name],
            _ => Vec::new(),
        })
        .collect::<BTreeSet<_>>();

    !block.stmts.iter().any(|stmt| match stmt {
        // 候选拒绝[SemanticBarrier:Scope]：Lua 5.5 repeat block 的词法范围包含 `until`
        // 条件；`local stop=true; repeat do global stop end until stop` 读取 local，拍平后
        // 却读取同名 global（direct AST unit 覆盖该拒绝形状）。
        AstStmt::GlobalDecl(_) => true,
        AstStmt::LocalDecl(local_decl) => {
            // 候选拒绝[SemanticBarrier:Lifetime]：`repeat do local x <close> = v end until cond()`
            // 拍平会把 `__close` 推迟到 cond 后；regress246 由 cond 断言逐轮 close 已发生。
            local_decl
                .bindings
                .iter()
                .any(|binding| binding.attr == AstLocalAttr::Close)
                // 候选拒绝[SemanticBarrier:Lifetime]：PhysicalRoot local 拍平后会在生成源码中
                // 活过 condition；lua54_01_close#18 用 `__gc` 证明未读 root 的域末可观察。
                || local_decl
                    .bindings
                    .iter()
                    .any(|binding| binding.origin == AstLocalOrigin::PhysicalRoot)
                // 候选拒绝[PolicyBoundary]：DebugHinted 的显式 repeat 内层词法域按源码证据保留。
                || local_decl
                    .bindings
                    .iter()
                    .any(|binding| binding.origin == AstLocalOrigin::DebugHinted)
                // 候选拒绝[SemanticBarrier:Lifetime]：repeat 尾 closure 拍平会让 closure 及
                // captured object 活过 condition；regress378 在 condition 中以 `__gc` 观察。
                || local_decl
                    .values
                    .iter()
                    .any(expr_contains_function)
        }
        // 候选拒绝[SemanticBarrier:Lifetime]：local function 与上述 closure 是同一 root
        // 延长；regress378 证明运行时差异，direct AST unit 覆盖 assign 表示。
        AstStmt::LocalFunctionDecl(_) => true,
        AstStmt::Assign(assign) => {
            // 候选拒绝[SemanticBarrier:Lifetime]：`local f; f=function() end` 的函数值由
            // 当前 do 内 local 持有；拍平会让该 root 活过 condition。Temp/SyntheticLocal
            // 是 AST build 暂时提升到函数根部的声明，保留 do 后 statement-merge 才能把它
            // 下沉回准确的词法 owner；regress378 覆盖该 bytecode 路径。真正的外层 source
            // local 不扩大当前 do 的任何 binding 生命周期。
            assign.values.iter().any(expr_contains_function)
                && assign.targets.iter().any(|target| {
                    matches!(
                        target,
                        AstLValue::Name(name)
                            if AstBindingRef::from_name_ref(name)
                                .is_some_and(|binding| nested_or_hoisted_binding(
                                    binding,
                                    &scoped_bindings
                                ))
                    )
                })
        }
        AstStmt::FunctionDecl(function_decl) => {
            let path = match &function_decl.target {
                AstFunctionName::Plain(path) | AstFunctionName::Method(path, _) => path,
            };
            // 候选拒绝[SemanticBarrier:Lifetime]：`local holder={}; function holder.f() end`
            // 让当前 do 的 holder 持有函数 root；拍平会把 holder 延寿到 condition 之后。
            AstBindingRef::from_name_ref(&path.root)
                .is_some_and(|binding| nested_or_hoisted_binding(binding, &scoped_bindings))
        }
        _ => {
            // 候选接受：其余语句不在 repeat 条件前引入 global、资源 local，或由当前
            // do binding 持有的 closure root；展开只删除机械缩进，控制流和求值顺序不变。
            false
        }
    })
}

fn nested_or_hoisted_binding(
    binding: AstBindingRef,
    scoped_bindings: &BTreeSet<AstBindingRef>,
) -> bool {
    scoped_bindings.contains(&binding)
        || matches!(
            binding,
            AstBindingRef::Temp(_) | AstBindingRef::SyntheticLocal(_)
        )
}

fn expr_contains_function(expr: &AstExpr) -> bool {
    if matches!(expr, AstExpr::FunctionExpr(_)) {
        return true;
    }
    let mut found = false;
    traverse_expr_children!(
        expr,
        iter = iter,
        borrow = [&],
        expr(child) => {
            found |= expr_contains_function(child);
        },
        function(_function) => {
            found = true;
        }
    );
    found
}

fn can_elide_single_stmt_do_block(stmt: &AstStmt) -> bool {
    match stmt {
        AstStmt::Assign(_)
        | AstStmt::CallStmt(_)
        | AstStmt::Return(_)
        | AstStmt::If(_)
        | AstStmt::While(_)
        | AstStmt::Repeat(_)
        | AstStmt::NumericFor(_)
        | AstStmt::GenericFor(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::Label(_) => {
            // 候选接受：唯一语句不声明外层可见 binding；label/goto 使用稳定 AstLabelId，
            // 生成名也由 ID 唯一确定，删除空 do 不会重新绑定已有控制流边。
            true
        }
        // 候选拒绝[SemanticBarrier:Lifetime]：单句 local 移出 do 会把对象 root/`<close>`
        // 延长到父域末；lua54_01_close#18 与 regress246 分别观察普通 root 和 close 时点。
        AstStmt::LocalDecl(_) => false,
        // 候选拒绝[SemanticBarrier:Scope]：`do global x=1 end; print(x)` 在 Lua 5.5 中
        // 原形拒绝未声明 x，拍平后却打印 1；global declaration 不能越过普通父块后继。
        AstStmt::GlobalDecl(_) => false,
        // 候选拒绝[SemanticBarrier:Scope]：`do local function f() end end; print(f)` 原形
        // 读取 global f，拍平后读取新 local f。
        AstStmt::LocalFunctionDecl(_) => false,
        // 候选接受：外层 do 内只有另一个 do，所有声明/label/goto 仍受内层 block 约束；
        // 删除空的外层词法层不扩大任何内部 binding 或控制流实体的作用域。
        AstStmt::DoBlock(_) => true,
        // 候选拒绝[LayerBoundary]：Error 由前层诊断 owner 保留，readability 不消费。
        AstStmt::Error(_) => false,
    }
}

struct BlockBindingFlow {
    mention_counts: BTreeMap<AstBindingRef, usize>,
    use_index: BindingUseIndex,
}

impl BlockBindingFlow {
    fn new(block: &AstBlock, trailing_condition: Option<&AstExpr>) -> Self {
        let mut mention_counts = BTreeMap::<AstBindingRef, usize>::new();
        for stmt in &block.stmts {
            for binding in binding_mentions_in_stmt(stmt) {
                *mention_counts.entry(binding).or_default() += 1;
            }
        }
        if let Some(condition) = trailing_condition {
            for binding in super::binding_flow::binding_mentions_in_expr(condition) {
                *mention_counts.entry(binding).or_default() += 1;
            }
        }
        let use_index =
            BindingUseIndex::for_stmts_with_trailing_expr(&block.stmts, trailing_condition);
        Self {
            mention_counts,
            use_index,
        }
    }

    fn mentioned_outside_own_decl(&self, binding: AstBindingRef) -> bool {
        // local 声明自身也算一次 mention；只有声明外还有提及时，才需要保留词法槽位。
        self.mention_counts.get(&binding).copied().unwrap_or(0) > 1
    }

    fn used_or_captured(&self, binding: AstBindingRef) -> bool {
        self.use_index.count_uses_in_suffix(0, binding) != 0
    }

    fn keeps_decl_alive(&self, binding: AstBindingRef) -> bool {
        self.mentioned_outside_own_decl(binding) || self.used_or_captured(binding)
    }
}

fn collect_live_empty_bindings(
    block: &AstBlock,
    binding_flow: &BlockBindingFlow,
) -> BTreeSet<AstBindingRef> {
    let mut live_bindings = BTreeSet::new();
    for stmt in &block.stmts {
        let AstStmt::LocalDecl(local_decl) = stmt else {
            continue;
        };
        for binding in &local_decl.bindings {
            if binding_flow.keeps_decl_alive(binding.id) {
                live_bindings.insert(binding.id);
            }
        }
    }
    live_bindings
}

fn into_call_kind(expr: AstExpr) -> Result<AstCallKind, AstExpr> {
    match expr {
        AstExpr::Call(call) => Ok(AstCallKind::Call(call)),
        AstExpr::MethodCall(call) => Ok(AstCallKind::MethodCall(call)),
        AstExpr::SingleValue(inner) => {
            into_call_kind(*inner).map_err(|inner| AstExpr::SingleValue(Box::new(inner)))
        }
        other => Err(other),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::common::{
        AstAssign, AstCallExpr, AstFunctionDecl, AstFunctionExpr, AstGlobalDecl, AstGlobalName,
        AstLValue, AstLocalBinding, AstNamePath, AstNameRef,
    };
    use crate::hir::{HirProtoRef, LocalId, TempId};

    fn recovered_binding() -> AstLocalBinding {
        AstLocalBinding {
            id: AstBindingRef::Local(LocalId(0)),
            attr: AstLocalAttr::None,
            origin: AstLocalOrigin::Recovered,
        }
    }

    fn call_value() -> AstExpr {
        AstExpr::Call(Box::new(AstCallExpr {
            callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                text: "factory".to_owned(),
            })),
            args: vec![],
            method_name: None,
        }))
    }

    fn function_value() -> AstExpr {
        AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
            function: HirProtoRef(1),
            params: vec![],
            is_vararg: false,
            named_vararg: None,
            body: AstBlock::default(),
            captured_bindings: BTreeSet::new(),
            captured_params: BTreeSet::new(),
        }))
    }

    #[test]
    fn splits_recovered_call_result_before_direct_overwrite() {
        let binding = recovered_binding();
        let declaration = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![binding.clone()],
            values: vec![call_value()],
        }));
        let overwrite = AstStmt::Assign(Box::new(AstAssign {
            targets: vec![AstLValue::Name(binding.id.to_name_ref())],
            values: vec![AstExpr::Integer(9), call_value()],
        }));

        let (call, rewritten) = split_overwritten_call_result(&declaration, &overwrite)
            .expect("a recovered call result with a direct overwrite is safe to split");
        assert!(matches!(call, AstCallKind::Call(_)));
        assert_eq!(rewritten.bindings, vec![binding]);
        assert_eq!(rewritten.values, vec![AstExpr::Integer(9), call_value()]);
    }

    #[test]
    fn keeps_debug_and_later_rhs_reads_but_splits_same_id_initializer() {
        let mut debug_binding = recovered_binding();
        debug_binding.origin = AstLocalOrigin::DebugHinted;
        let debug_decl = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![debug_binding.clone()],
            values: vec![call_value()],
        }));
        let debug_write = AstStmt::Assign(Box::new(AstAssign {
            targets: vec![AstLValue::Name(debug_binding.id.to_name_ref())],
            values: vec![AstExpr::Integer(9)],
        }));
        assert!(split_overwritten_call_result(&debug_decl, &debug_write).is_none());

        let binding = recovered_binding();
        let self_call = AstExpr::Call(Box::new(AstCallExpr {
            callee: AstExpr::Var(binding.id.to_name_ref()),
            args: vec![],
            method_name: None,
        }));
        let declaration = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![binding.clone()],
            values: vec![self_call],
        }));
        let overwrite = AstStmt::Assign(Box::new(AstAssign {
            targets: vec![AstLValue::Name(binding.id.to_name_ref())],
            values: vec![AstExpr::Integer(9)],
        }));
        let (call, _) = split_overwritten_call_result(&declaration, &overwrite)
            .expect("the call stays before the local lexical scope in both shapes");
        let AstCallKind::Call(call) = call else {
            panic!("same-id initializer should preserve the direct call");
        };
        assert_eq!(call.callee, AstExpr::Var(binding.id.to_name_ref()));

        let declaration = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![binding.clone()],
            values: vec![call_value()],
        }));
        let later_rhs_read = AstStmt::Assign(Box::new(AstAssign {
            targets: vec![AstLValue::Name(binding.id.to_name_ref())],
            values: vec![AstExpr::Integer(9), AstExpr::Var(binding.id.to_name_ref())],
        }));
        assert!(split_overwritten_call_result(&declaration, &later_rhs_read).is_none());
    }

    #[test]
    fn keeps_repeat_tail_global_declaration_scope() {
        let block = AstBlock {
            stmts: vec![AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
                bindings: vec![],
                values: vec![],
            }))],
        };

        assert!(!trailing_do_block_is_scope_neutral(&block, true));
        assert!(trailing_do_block_is_scope_neutral(&block, false));
    }

    #[test]
    fn keeps_repeat_tail_closure_roots_owned_by_nested_locals() {
        let binding = recovered_binding();
        let assigned_closure = AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![binding.clone()],
                    values: vec![],
                })),
                AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::Name(binding.id.to_name_ref())],
                    values: vec![function_value()],
                })),
            ],
        };
        assert!(!trailing_do_block_is_scope_neutral(&assigned_closure, true));

        let hoisted_temp = AstBindingRef::Temp(TempId(7));
        let hoisted_closure = AstBlock {
            stmts: vec![AstStmt::Assign(Box::new(AstAssign {
                targets: vec![AstLValue::Name(hoisted_temp.to_name_ref())],
                values: vec![AstExpr::SingleValue(Box::new(function_value()))],
            }))],
        };
        assert!(!trailing_do_block_is_scope_neutral(&hoisted_closure, true));

        let rooted_function_decl = AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![binding.clone()],
                    values: vec![],
                })),
                AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
                    target: AstFunctionName::Plain(AstNamePath {
                        root: binding.id.to_name_ref(),
                        fields: vec!["method".to_owned()],
                    }),
                    func: match function_value() {
                        AstExpr::FunctionExpr(function) => *function,
                        _ => unreachable!(),
                    },
                })),
            ],
        };
        assert!(!trailing_do_block_is_scope_neutral(
            &rooted_function_decl,
            true
        ));

        let outer_binding = AstBindingRef::Local(LocalId(99));
        let outer_assignment = AstBlock {
            stmts: vec![AstStmt::Assign(Box::new(AstAssign {
                targets: vec![AstLValue::Name(outer_binding.to_name_ref())],
                values: vec![function_value()],
            }))],
        };
        assert!(trailing_do_block_is_scope_neutral(&outer_assignment, true));
    }
}
