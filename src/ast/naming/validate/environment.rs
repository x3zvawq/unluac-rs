//! 在命名前校验局部环境身份的词法活动范围。
//!
//! 消费 HIR 发布的环境角色与当前 AST，拒绝已失去活动声明的隐式 global 绑定。

use std::ops::ControlFlow;

use crate::ast::traverse::BlockKind;
use crate::ast::visit::{AstVisitor, NameAccess, visit_stmt};
use crate::ast::{
    AstBindingRef, AstBlock, AstExpr, AstFunctionExpr, AstLocalAttr, AstNameRef, AstStmt,
};
use crate::hir::{HirProto, LocalId};

use super::NamingError;

pub(super) fn validate(body: &AstBlock, proto: &HirProto) -> Result<(), NamingError> {
    let Some(local) = proto.lexical_environment_local else {
        return Ok(());
    };
    let mut validator = EnvironmentScope {
        local,
        active: false,
        declarations: 0,
        globals: 0,
        invalid: !proto.environment_upvalues.is_empty(),
    };
    validator.visit_block(body, BlockKind::Regular);
    if validator.invalid || validator.declarations != 1 || validator.globals == 0 {
        return Err(NamingError::InvalidLexicalEnvironment {
            function: proto.id.index(),
            reason: "expected one ordinary environment snapshot active at every global declaration",
        });
    }
    Ok(())
}

struct EnvironmentScope {
    local: LocalId,
    active: bool,
    declarations: usize,
    globals: usize,
    invalid: bool,
}

impl AstVisitor for EnvironmentScope {
    fn visit_block(&mut self, block: &AstBlock, _kind: BlockKind) -> bool {
        let outer_active = self.active;
        for stmt in &block.stmts {
            visit_stmt(stmt, self);
        }
        self.active = outer_active;
        false
    }

    fn visit_stmt(&mut self, stmt: &AstStmt) {
        match stmt {
            AstStmt::GlobalDecl(_) => {
                self.globals += 1;
                self.invalid |= !self.active;
            }
            AstStmt::LocalDecl(decl)
                if decl
                    .bindings
                    .iter()
                    .any(|binding| binding.id == AstBindingRef::Local(self.local)) =>
            {
                self.declarations += 1;
                self.invalid |= decl.bindings.len() != 1
                    || decl.bindings[0].attr != AstLocalAttr::None
                    || !matches!(
                        decl.values.as_slice(),
                        [AstExpr::Var(AstNameRef::Upvalue(_) | AstNameRef::Param(_))]
                    );
            }
            // 当前 HIR 证书不覆盖跳转/循环的活动范围；Do 的直线词法嵌套可以消费。
            AstStmt::If(_)
            | AstStmt::While(_)
            | AstStmt::Repeat(_)
            | AstStmt::NumericFor(_)
            | AstStmt::GenericFor(_)
            | AstStmt::Goto(_)
            | AstStmt::Label(_) => self.invalid = true,
            _ => {}
        }
    }

    fn leave_stmt(&mut self, stmt: &AstStmt) {
        if let AstStmt::LocalDecl(decl) = stmt
            && decl
                .bindings
                .iter()
                .any(|binding| binding.id == AstBindingRef::Local(self.local))
        {
            // RHS 完成求值后局部名字才生效，不能遮蔽自己的源 upvalue。
            self.active = true;
        }
    }

    fn visit_name(&mut self, name: &AstNameRef, access: NameAccess) -> ControlFlow<()> {
        if *name == AstNameRef::Environment {
            self.invalid = true;
        }
        if *name == AstNameRef::Local(self.local) {
            self.invalid |= match access {
                NameAccess::Read => !self.active,
                NameAccess::LocalDeclaration => false,
                _ => true,
            };
        }
        ControlFlow::Continue(())
    }

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        self.invalid = true;
        false
    }
}
