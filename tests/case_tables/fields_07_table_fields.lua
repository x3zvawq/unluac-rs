-- 确定字段值允许深层私有构造器折叠；GC输出始终比较各VM自己的源码基线。
-- stripped产物的外层字段不能重新拆成独立store；debug保留源码identity另由运行验证。
-- unluac: expect-not-contains [[r1_0.root =]]
-- unluac: expect-not-contains [[r3_1.branches =]]
local function record_chain()
    local tree = {root = {branch = {score = 4}}}
    return tree.root.branch.score
end
local function array_chain()
    local tree = {nodes = {{score = 4}, {score = 9}}}
    return tree.nodes[2].score
end
local function selected_field()
    local keys = {"left", "right"}
    local tree = {branches = {left = {score = 4}, right = {score = 9}}}
    local selected = tree.branches[keys[2]]
    selected.score = selected.score + tree.branches[keys[1]].score
    return selected.score, selected == tree.branches.right
end
assert(record_chain() == 4 and array_chain() == 9)
local score, same = selected_field()
assert(score == 13 and same)
print("private-fields", record_chain(), array_chain(), score, same)

local weak = setmetatable({}, {__mode = "v"})
local function observe(label)
    collectgarbage("collect")
    collectgarbage("collect")
    print(label, weak.value ~= nil)
end
local function publish(value)
    weak.value = value
end
local function resource()
    local value = {}
    weak.value = value
    return value
end

-- 子表曾逃逸后再清除字段，不能凭最终为空撤销历史。
local function escaped_child()
    local tree = {nodes = {4, 9}}
    publish(tree.nodes)
    tree.nodes = nil
    observe("escaped-child")
end
escaped_child()

-- 初始常量子表后来持有外部资源，独立子表根可能继续保活资源。
local function inserted_resource(value)
    local tree = {nodes = {4, 9}}
    tree.nodes.payload = value
    value = nil
    tree.nodes = nil
    observe("inserted-resource")
end
inserted_resource(resource())

-- 弱表写入本身就是外部观察；不能把确定字段关系解释为强持有。
local weak_keys = setmetatable({}, {__mode = "k"})
local function weak_key()
    local tree = {nodes = {4, 9}}
    weak_keys[tree.nodes] = true
    tree.nodes = nil
    collectgarbage("collect")
    collectgarbage("collect")
    print("weak-key", next(weak_keys) ~= nil)
end
weak_key()

local proxy = setmetatable({}, {__index = function(_, key)
    observe("lookup-" .. key)
    return 7
end})
local function callback_lookup()
    local tree = {nodes = {4, 9}}
    publish(tree.nodes)
    tree.nodes = nil
    return proxy.result
end
assert(callback_lookup() == 7)

-- 多目标写入的RHS来自同一旧快照；第二个读取不能看到第一个写入。
local function parallel_fields()
    local tree = {nodes = {left = {score = 4}, right = {score = 9}}}
    tree.nodes.left, tree.nodes.right = tree.nodes.right, tree.nodes.left
    return tree.nodes.left.score, tree.nodes.right.score
end
local left, right = parallel_fields()
assert(left == 9 and right == 4)
print("parallel-fields", left, right)

-- 私有initializer旁有独立资源根；折叠不得新增local或扩大它的物理生存期。
local function neighboring_root(methods)
    local side = resource()
    local tree = {nodes = {{score = 4}}}
    local node = tree.nodes[1]
    side = nil
    local callback = methods.check
    callback("neighbor-root")
    return node.score, side == nil
end
local methods = setmetatable({}, {__index = function(_, key)
    observe("neighbor-lookup-" .. key)
    return observe
end})
local result, cleared = neighboring_root(methods)
assert(result == 4 and cleared)

-- 引用cell在nil时已经公开，之后写入fresh alias同样可被外部callback访问。
local function captured_cell()
    local captured
    local access = setmetatable({}, {__index = function()
        local value = {}
        weak.value = value
        captured.nodes.payload = value
        value = nil
        captured.nodes = nil
        observe("captured-cell")
        return 7
    end})
    local inner = {nodes = {4, 9}}
    captured = inner
    local answer = access.lookup
    return answer
end
assert(captured_cell() == 7)
