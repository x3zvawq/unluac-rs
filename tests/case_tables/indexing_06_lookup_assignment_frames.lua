-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=1]]
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@proto=2]]
-- unluac: expect-ast-count [[assign]] [[2]] [[@proto=2]]
-- unluac: expect-ast-max [[local-binding]] [[2]] [[@proto=3]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=3]]
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@proto=4]]
-- unluac: expect-ast-count [[assign]] [[2]] [[@proto=4]]
-- 多层目标表快照、动态索引初始化与普通算术共用完整原槽帧。
-- unluac: expect-not-contains [[= print]]
-- unluac: expect-contains [[.values[1] = ]]
-- unluac: expect-contains [[string.upper(string.sub(]]
local function deep()
    local t = {root = {nodes = {
        {id = "a", values = {1, 2}}, {id = "b", values = {3, 4}},
    }, flags = {open = true, closed = false}}}
    t.root.nodes[2].values[1] = t.root.nodes[1].values[2] + 5
    assert(t.root.nodes[1].id == "a" and t.root.nodes[2].id == "b")
    assert(t.root.nodes[1].values[1] == 1 and t.root.nodes[1].values[2] == 2)
    assert(t.root.nodes[2].values[1] == 7 and t.root.nodes[2].values[2] == 4)
    assert(t.root.flags.open == true and t.root.flags.closed == false and #t.root.nodes == 2)
    print("deep", t.root.nodes[1].id, t.root.nodes[2].values[1], t.root.flags.open, #t.root.nodes)
end
local function dynamic()
    local keys = {"left", "right"}
    local t = {branches = {left = {score = 4}, right = {score = 9}}}
    local selected = t.branches[keys[2]]
    selected.score = selected.score + t.branches[keys[1]].score
    t.branches[keys[1]].score = selected.score - 3
    assert(t.branches.left.score == 10 and t.branches.right.score == 13)
    assert(selected == t.branches.right and selected ~= t.branches.left)
    print("dynamic", t.branches.left.score, t.branches.right.score, selected == t.branches.right)
end
local function arithmetic()
    local t = {[1] = "hex", key = {inner = 42}, 1, 2, 3}
    t[1] = t.key.inner + t[2] + #t
    local text = string.upper(string.sub(t[1] .. "hello", 1, 5))
    return t, text
end
local function overwrite()
    local suffix = "tail"
    local key = "slot_" .. suffix
    local t = {list = {10, 20, 30}, meta = {[key] = 7}}
    t.list[2] = t.list[1] + t.meta[key]
    t.meta[key] = t.list[3] - t.list[2]
    assert(t.list[1] == 10 and t.list[2] == 17 and t.list[3] == 30)
    assert(t.meta[key] == 13 and t.meta.slot_tail == 13)
    print("overwrite", t.list[1], t.list[2], t.list[3], t.meta[key], t.meta.slot_tail)
end
deep()
dynamic()
overwrite()
local result, text = arithmetic()
assert(result[1] == 47 and text == "47HEL")
print("arithmetic", result[1], text)
