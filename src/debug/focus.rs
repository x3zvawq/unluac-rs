//! 这个文件承载所有 dump 层共享的「聚焦 proto + 限深展开」模型。
//!
//! 为什么要有这个文件：
//! - `tests/lua_cases/*.lua` 里一个根 proto 常嵌十几个子 case proto，
//!   旧的 `DebugFilters::proto` 只能做「全量」或「只看那个 proto」两档，
//!   导致默认 dump 爆炸、传 `--proto` 又看不到子 proto 存在性。
//! - 我们需要一个跨所有 dump 层统一的「聚焦」模型：给定焦点 proto 和
//!   向下展开的层数，计算出哪些 proto 要完整渲染、哪些用一行 summary 占位。
//! - 把这个计算下放到每个 dump 层各自写一份会产生漂移，尤其容易在「什么时候
//!   该打 elided 行」上出 bug，所以集中到这个文件，让每层传一颗 proto 树就行。
//!
//! 这个文件不承担业务事实的查询：各层自己决定在 elided 行里填哪些字段，
//! 这里只提供容器 `ProtoSummaryRow` 和稳定格式 `format_proto_summary_row`。
//!
//! 输入形状 -> 输出形状例子：
//!   protos=[(id=0, parent=-), (id=1, parent=0), (id=2, parent=1)]
//!   filters={ proto=None, proto_depth=Fixed(0) }
//!     -> FocusPlan{ focus=Some(0), visible={0}, elided_at=[1] }
//!   filters={ proto=Some(1), proto_depth=Fixed(0) }
//!     -> FocusPlan{ focus=Some(1), visible={1}, elided_at=[2], ancestors=[0] }
//!   filters={ proto=None, proto_depth=All }
//!     -> FocusPlan{ focus=Some(0), visible={0,1,2}, elided_at=[] }

use std::collections::BTreeSet;
use std::fmt::{self, Write as _};

/// proto 向下展开的层数语义。
///
/// `Fixed(N)` 表示相对焦点 proto 向下展开 N 层；`All` 表示不设上限（等价于旧的全量行为）。
/// 默认值 `Fixed(0)` 意味着只展开焦点本身，子 proto 以占位行出现。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum ProtoDepth {
    Fixed(usize),
    All,
}

impl Default for ProtoDepth {
    fn default() -> Self {
        Self::Fixed(0)
    }
}

impl ProtoDepth {
    /// 判断给定的相对深度是否仍在展开范围内。
    ///
    /// `relative == 0` 表示焦点自身，一定在范围内。
    pub fn includes(self, relative: usize) -> bool {
        match self {
            Self::Fixed(limit) => relative <= limit,
            Self::All => true,
        }
    }
}

impl fmt::Display for ProtoDepth {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Fixed(n) => write!(f, "{n}"),
            Self::All => f.write_str("all"),
        }
    }
}

/// proto 树节点的轻量描述，供 `compute_focus_plan` 消费。
///
/// 每个 `ProtoNode` 在 `nodes` 切片里的下标就是它的稳定 id（DFS 序），
/// 各层在调用本 helper 前要自己先把树线性化成这个形态。
#[derive(Debug, Clone)]
pub struct ProtoNode {
    pub parent: Option<usize>,
    pub children: Vec<usize>,
}

/// 从 DFS 序的 `(id, parent)` 对列表反推 `Vec<ProtoNode>`。
///
/// 各层 dump 之前已经用 DFS 把 proto 展平成线性数组，只是不一定保存了
/// `parent`。这个 helper 允许层自己决定是否跟踪 parent，再统一交由 focus 计算。
/// 要求 `id` 等于 `parents.len() - 1 - idx_in_reverse`，也就是 `(id, parent)`
/// 按 DFS 顺序 push 进来即可。
pub fn build_proto_nodes(parents: &[Option<usize>]) -> Vec<ProtoNode> {
    let mut nodes: Vec<ProtoNode> = (0..parents.len())
        .map(|_| ProtoNode {
            parent: None,
            children: Vec::new(),
        })
        .collect();
    for (id, parent) in parents.iter().enumerate() {
        nodes[id].parent = *parent;
        if let Some(parent) = parent
            && *parent < nodes.len()
        {
            nodes[*parent].children.push(id);
        }
    }
    nodes
}

/// `compute_focus_plan` 的结果。
///
/// - `focus`：最终选中的聚焦 proto id。`None` 表示用户指定的 id 不存在。
/// - `ancestors`：从根到焦点父节点（含根，不含焦点）的路径，供 breadcrumb 使用。
/// - `visible`：需要完整渲染的 proto id 集合（包含焦点本身）。
/// - `elided_at`：需要以 summary 行占位的 proto id，按 DFS 序排列。
#[derive(Debug, Clone, Default)]
pub struct FocusPlan {
    pub focus: Option<usize>,
    pub ancestors: Vec<usize>,
    pub visible: BTreeSet<usize>,
    pub elided_at: Vec<usize>,
}

impl FocusPlan {
    pub fn is_visible(&self, id: usize) -> bool {
        self.visible.contains(&id)
    }

    pub fn is_elided(&self, id: usize) -> bool {
        self.elided_at.contains(&id)
    }
}

/// 基于一颗 proto 树和聚焦参数计算可见/省略集合。
///
/// 当 `focus` 指向的 id 不存在时，返回空 plan：所有 proto 都被隐藏，
/// 调用方应显示类似 `<no proto matched filters>` 的提示。
pub fn compute_focus_plan(nodes: &[ProtoNode], filters: &FocusRequest) -> FocusPlan {
    if nodes.is_empty() {
        return FocusPlan::default();
    }

    // 默认焦点 = 0（入口 proto）。这和「默认只看根 proto」的约定一致。
    let focus_id = filters.proto.unwrap_or(0);
    if focus_id >= nodes.len() {
        return FocusPlan::default();
    }

    // 从焦点向上回溯祖先，便于渲染 breadcrumb。
    let mut ancestors = Vec::new();
    let mut cursor = nodes[focus_id].parent;
    while let Some(parent) = cursor {
        ancestors.push(parent);
        cursor = nodes[parent].parent;
    }
    ancestors.reverse();

    // 从焦点向下按相对深度 BFS 扩展可见集合，
    // 同时把被裁掉的直接子节点加入 `elided_at`，保证在 DFS 原序中出现。
    let mut visible = BTreeSet::new();
    let mut elided_at = Vec::new();
    walk_below(nodes, focus_id, 0, filters.depth, &mut visible, &mut elided_at);

    FocusPlan {
        focus: Some(focus_id),
        ancestors,
        visible,
        elided_at,
    }
}

fn walk_below(
    nodes: &[ProtoNode],
    node_id: usize,
    relative_depth: usize,
    depth: ProtoDepth,
    visible: &mut BTreeSet<usize>,
    elided_at: &mut Vec<usize>,
) {
    if !depth.includes(relative_depth) {
        elided_at.push(node_id);
        return;
    }
    visible.insert(node_id);
    for child in &nodes[node_id].children {
        walk_below(nodes, *child, relative_depth + 1, depth, visible, elided_at);
    }
}

/// 聚焦参数的最小输入。`DebugFilters` 与 pass dump config 都能投射到这个结构。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Default)]
pub struct FocusRequest {
    pub proto: Option<usize>,
    pub depth: ProtoDepth,
}

/// 每个 dump 层需要打印 elided 占位行时，把可获得的辨识信息放进这个 struct，
/// 再用 `format_proto_summary_row` 渲染成稳定格式的单行文本。
///
/// 不是每一层都能填齐所有字段：
/// - parser / transformer / cfg / graph-facts / dataflow / structure 只有
///   `lines / instrs / children / first`（`name=-`）。
/// - HIR / AST / readability / naming / generate 可额外填 `name`。
#[derive(Debug, Clone, Default)]
pub struct ProtoSummaryRow {
    pub id: usize,
    pub depth_below_focus: usize,
    pub name: Option<String>,
    pub first: Option<String>,
    pub lines: Option<(u32, u32)>,
    pub instrs: Option<usize>,
    pub children: Option<usize>,
}

/// 渲染单个 elided 占位行。
///
/// 约定格式（方便肉眼扫描）：
///   `proto#<id> <elided> name=<n> lines=<A..B> first=<"..."> instrs=<K> children=<C>`
///
/// 缺失的字段统一用 `-` 占位；`first` 会做长度截断避免一行爆炸。
pub fn format_proto_summary_row(row: &ProtoSummaryRow) -> String {
    let mut output = String::new();
    let _ = write!(output, "proto#{} <elided>", row.id);

    let name = row.name.as_deref().unwrap_or("-");
    let _ = write!(output, " name={name}");

    match row.lines {
        Some((start, end)) => {
            let _ = write!(output, " lines={start}..{end}");
        }
        None => {
            let _ = write!(output, " lines=-");
        }
    }

    let first_rendered = row
        .first
        .as_deref()
        .map(truncate_first)
        .unwrap_or_else(|| "-".to_owned());
    let _ = write!(output, " first={first_rendered}");

    if let Some(instrs) = row.instrs {
        let _ = write!(output, " instrs={instrs}");
    }
    if let Some(children) = row.children {
        let _ = write!(output, " children={children}");
    }

    output
}

const FIRST_SNIPPET_MAX_CHARS: usize = 80;

fn truncate_first(raw: &str) -> String {
    let mut snippet = String::new();
    for (count, ch) in raw.chars().enumerate() {
        if ch == '\n' || ch == '\r' {
            break;
        }
        if count >= FIRST_SNIPPET_MAX_CHARS {
            snippet.push('…');
            break;
        }
        snippet.push(ch);
    }
    format!("\"{snippet}\"")
}

/// 渲染 breadcrumb 行（`focus proto#<id> path=proto#A -> proto#B -> ...`）。
///
/// 当焦点就是入口 proto 且无祖先时，返回 `None`，让调用方自己决定是否跳过这行。
pub fn format_breadcrumb(plan: &FocusPlan) -> Option<String> {
    let focus = plan.focus?;
    if plan.ancestors.is_empty() {
        return None;
    }

    let mut output = format!("focus proto#{focus} path=");
    let mut first = true;
    for ancestor in &plan.ancestors {
        if !first {
            output.push_str(" -> ");
        }
        first = false;
        let _ = write!(output, "proto#{ancestor}");
    }
    let _ = write!(output, " -> proto#{focus}");
    Some(output)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_tree() -> Vec<ProtoNode> {
        // tree:
        //   0
        //   ├─ 1
        //   │  └─ 2
        //   └─ 3
        vec![
            ProtoNode {
                parent: None,
                children: vec![1, 3],
            },
            ProtoNode {
                parent: Some(0),
                children: vec![2],
            },
            ProtoNode {
                parent: Some(1),
                children: vec![],
            },
            ProtoNode {
                parent: Some(0),
                children: vec![],
            },
        ]
    }

    #[test]
    fn default_focus_is_root_with_depth_zero() {
        let plan = compute_focus_plan(
            &make_tree(),
            &FocusRequest {
                proto: None,
                depth: ProtoDepth::Fixed(0),
            },
        );
        assert_eq!(plan.focus, Some(0));
        assert!(plan.ancestors.is_empty());
        assert_eq!(plan.visible.iter().copied().collect::<Vec<_>>(), vec![0]);
        assert_eq!(plan.elided_at, vec![1, 3]);
    }

    #[test]
    fn depth_one_expands_direct_children_and_elides_grandchildren() {
        let plan = compute_focus_plan(
            &make_tree(),
            &FocusRequest {
                proto: None,
                depth: ProtoDepth::Fixed(1),
            },
        );
        assert_eq!(plan.visible.iter().copied().collect::<Vec<_>>(), vec![0, 1, 3]);
        assert_eq!(plan.elided_at, vec![2]);
    }

    #[test]
    fn all_depth_is_fully_visible() {
        let plan = compute_focus_plan(
            &make_tree(),
            &FocusRequest {
                proto: None,
                depth: ProtoDepth::All,
            },
        );
        assert_eq!(
            plan.visible.iter().copied().collect::<Vec<_>>(),
            vec![0, 1, 2, 3]
        );
        assert!(plan.elided_at.is_empty());
    }

    #[test]
    fn focus_on_child_records_ancestors() {
        let plan = compute_focus_plan(
            &make_tree(),
            &FocusRequest {
                proto: Some(2),
                depth: ProtoDepth::Fixed(0),
            },
        );
        assert_eq!(plan.focus, Some(2));
        assert_eq!(plan.ancestors, vec![0, 1]);
        assert_eq!(plan.visible.iter().copied().collect::<Vec<_>>(), vec![2]);
        assert!(plan.elided_at.is_empty());
    }

    #[test]
    fn unknown_focus_yields_empty_plan() {
        let plan = compute_focus_plan(
            &make_tree(),
            &FocusRequest {
                proto: Some(99),
                depth: ProtoDepth::Fixed(0),
            },
        );
        assert_eq!(plan.focus, None);
        assert!(plan.visible.is_empty());
        assert!(plan.elided_at.is_empty());
    }

    #[test]
    fn format_row_renders_stable_shape() {
        let row = ProtoSummaryRow {
            id: 5,
            depth_below_focus: 1,
            name: Some("test_setfenv".to_owned()),
            first: Some("local function read_value()".to_owned()),
            lines: Some((3, 6)),
            instrs: Some(27),
            children: Some(2),
        };
        assert_eq!(
            format_proto_summary_row(&row),
            r#"proto#5 <elided> name=test_setfenv lines=3..6 first="local function read_value()" instrs=27 children=2"#
        );
    }

    #[test]
    fn format_row_truncates_long_first() {
        let row = ProtoSummaryRow {
            id: 1,
            depth_below_focus: 0,
            name: None,
            first: Some("a".repeat(200)),
            lines: None,
            instrs: None,
            children: None,
        };
        let text = format_proto_summary_row(&row);
        assert!(text.contains("…"));
        assert!(!text.contains(&"a".repeat(150)));
    }

    #[test]
    fn breadcrumb_is_skipped_when_no_ancestors() {
        let plan = FocusPlan {
            focus: Some(0),
            ancestors: Vec::new(),
            visible: BTreeSet::from([0]),
            elided_at: Vec::new(),
        };
        assert!(format_breadcrumb(&plan).is_none());
    }

    #[test]
    fn breadcrumb_renders_path() {
        let plan = FocusPlan {
            focus: Some(2),
            ancestors: vec![0, 1],
            visible: BTreeSet::from([2]),
            elided_at: Vec::new(),
        };
        assert_eq!(
            format_breadcrumb(&plan).as_deref(),
            Some("focus proto#2 path=proto#0 -> proto#1 -> proto#2")
        );
    }
}
