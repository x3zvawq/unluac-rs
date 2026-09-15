//! 固定参数 FASTCALL 在完整帧树中的统一准备协议。
//!
//! Promotion 提供 builtin、direct/COPY 掩码和原调用槽；共享 builder 按原顺序消费
//! 参数、fallback lookup 与 dispatch，外层 native owner 再验证声明前缀和生命周期。
//! 例如 `table.insert(t, tonumber("1"))` 的内层开放结果仍是 FASTCALL，不能交给
//! 普通 CALL 的 callee-first 入口；独立调用与嵌套调用共用同一证明，不重建第二份事实。

use super::*;

/// 原 FASTCALL 已签发 builtin 身份，重建仍须保留裸全局或库字段拼写以重发快路径。
pub(super) fn callee_is_named(callee: &HirExpr) -> bool {
    let identifier = |name: &crate::lua_string::LuaString| {
        name.as_utf8()
            .is_some_and(|name| DecompileDialect::Luau.is_identifier_name(name))
    };
    match callee {
        HirExpr::GlobalRef(global) => identifier(&global.key),
        HirExpr::TableAccess(access) => matches!((&access.base, &access.key),
            (HirExpr::GlobalRef(global), HirExpr::String(key)) if identifier(&global.key) && identifier(key)),
        _ => false,
    }
}

impl FrameBuilder<'_> {
    pub(super) fn fastcall_fixed(
        &mut self,
        call: &HirCallExpr,
        before: usize,
        slot: usize,
        width: CallWidth,
    ) -> Option<HirCallExpr> {
        self.native?;
        let facts = self.facts;
        let dialect = self.dialect;
        let protocol @ crate::transformer::FastCallProtocol::Mask {
            direct_tail: false, ..
        } = call.fastcall?
        else {
            return None;
        };
        if dialect != DecompileDialect::Luau
            || call.method != HirMethodCall::None
            || call.args.tail.is_some()
            || !(1..=3).contains(&call.args.fixed.len())
        {
            return None;
        }
        let frame = facts.native_fastcall_frame(call)?;
        let ValuePack::Fixed(args) = frame.args else {
            return None;
        };
        if frame.home.slot() != slot
            || args.len != call.args.fixed.len()
            || args.start.index() != frame.home.slot() + 1
            || !match (width, frame.results) {
                (CallWidth::Ignore, Some(ResultPack::Ignore)) => true,
                (CallWidth::Single, Some(ResultPack::Fixed(pack))) => {
                    pack.start.index() == frame.home.slot() && pack.len == 1
                }
                (CallWidth::Open, Some(ResultPack::Open(start))) => start.index() == slot,
                _ => false,
            }
            || !frame.arguments_unaliased
        {
            return None;
        }
        let copies = facts.fastcall_argument_copies(call)?;
        if copies.len()
            != (0..args.len)
                .filter(|index| !protocol.fixed_is_direct(*index))
                .count()
        {
            return None;
        }

        let mut arguments = vec![None; args.len];
        let mut copies = copies.iter();
        for prepare_direct in [true, false] {
            for (index, argument) in call.args.fixed.iter().enumerate() {
                let direct = protocol.fixed_is_direct(index);
                let embedded = protocol.fixed_is_embedded_constant(index);
                if (direct && !embedded) != prepare_direct {
                    continue;
                }
                let slot = args.start.index() + index;
                if direct {
                    let value = self.expr(
                        argument,
                        before,
                        slot,
                        None,
                        false,
                        true,
                        facts.call_argument_value(call, index),
                    )?;
                    let literal = matches!(
                        value,
                        HirExpr::Nil
                            | HirExpr::Boolean(_)
                            | HirExpr::Integer(_)
                            | HirExpr::Number(_)
                            | HirExpr::String(_)
                    );
                    let lookup = !embedded
                        && matches!(&value, HirExpr::TableAccess(access)
                if facts.table_read_result_home(access) == Some(HomeSlotKey::new(slot, 0))
                    && facts.native_table_read_layout(access).is_some_and(|layout|
                        layout.key.is_none()
                            && layout.base.slot() < frame.home.slot()
                            && self.direct_home(&access.base) == Some(layout.base)));
                    // CALL 的单结果与完整原槽准备由 self.call 签证；direct 阶段仍先于
                    // fallback COPY/lookup，不能借此移动未纳入同一事务的根释放。
                    let call = !embedded && matches!(value, HirExpr::Call(_));
                    // compileExprFastcallN 对非 local 参数调用 compileExprTempTop；已有
                    // builder 证明表字段/事件，原 allocation 还须落在当前 direct 参数槽。
                    let table = !embedded
                        && matches!(&value, HirExpr::TableConstructor(table)
                        if facts.allocation_result_home(table).is_some_and(|home| home.slot() == slot));
                    // mixed FASTCALL 的 direct Boolean 与全 direct 参数共用原比较结果协议；
                    // message 的 fallback COPY 不改变这个参数先写入原槽的时点。
                    let comparison = !embedded
                        && matches!(&value, HirExpr::Binary(binary)
                    if self.luau_boolean_comparison(binary, slot));
                    let conditional_table = !embedded
                        && matches!(&value, HirExpr::LogicalOr(logical)
                        if self.luau_table_or_empty_layout(logical, before, slot).is_some());
                    // 嵌入常量不能变成有事件的 RHS；其余表达式尚无此准备协议的证明。
                    if !literal && !lookup && !call && !table && !comparison && !conditional_table {
                        return None;
                    }
                    arguments[index] = Some(value);
                    continue;
                }
                let copy = copies.next()?;
                if copy.argument != index
                    || copy.home != HomeSlotKey::new(slot, 0)
                    || copy.source_home.slot() >= frame.home.slot()
                {
                    return None;
                }
                let value = self.expr(
                    argument,
                    before,
                    slot,
                    None,
                    false,
                    true,
                    Some(copy.producer),
                )?;
                let home = match &value {
                    HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local),
                    HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param),
                    _ => None,
                };
                if home != Some(copy.source_home) {
                    return None;
                }
                arguments[index] = Some(value);
            }
        }
        let arguments = arguments.into_iter().collect::<Option<Vec<_>>>()?;
        let callee = self.expr(
            &call.callee,
            before,
            frame.home.slot(),
            None,
            true,
            false,
            Some(frame.callee),
        )?;
        // 全局 builtin 拼写保留原 FASTCALL 分类；不把一般函数别名当作重新产生快路径的证书。
        if !callee_is_named(&callee) {
            return None;
        }
        self.finish_dispatch(call, before)?;
        let rebuilt = HirCallExpr {
            callee,
            args: arguments.into(),
            method: call.method,
            method_key: call.method_key.clone(),
            callee_root_handoff: call.callee_root_handoff,
            method_rewrite_transaction: call.method_rewrite_transaction,
            plain_method_syntax: false,
            frame_root_ends: call.frame_root_ends.clone(),
            source_site: call.source_site,
            fastcall: call.fastcall,
            argument_roots: call.argument_roots.clone(),
        };
        Some(rebuilt)
    }
}
