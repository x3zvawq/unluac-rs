//! AST readability 里的 binding 名称身份转换。
//!
//! 这里承载不依赖语句流、不递归 AST 子树的纯查询：在 `AstNameRef` 和稳定
//! `AstBindingRef` 之间转换，以及判断一个名字是否指向指定 binding。更复杂的
//! use-count、捕获和树遍历继续放在 `binding_flow` / `binding_tree`。

use super::super::common::{AstBindingRef, AstNameRef};

pub(super) fn binding_from_name_ref(name: &AstNameRef) -> Option<AstBindingRef> {
    AstBindingRef::from_name_ref(name)
}

pub(super) fn name_ref_from_binding(binding: AstBindingRef) -> AstNameRef {
    binding.to_name_ref()
}

pub(super) fn name_matches_binding(name: &AstNameRef, binding: AstBindingRef) -> bool {
    binding.matches_name_ref(name)
}
