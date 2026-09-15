-- regress_510_return_lookup_value_dag: shared temp definitions must stay a DAG during root analysis.
-- The same source runs with numbers and observable __add calls; each definition executes once.
-- unluac: expect-ast-min [[local-decl]] [[25]]

return_dag_source = 3

local function run()
    local x0 = return_dag_source
    local x1 = x0 + x0
    local x2 = x1 + x1
    local x3 = x2 + x2
    local x4 = x3 + x3
    local x5 = x4 + x4
    local x6 = x5 + x5
    local x7 = x6 + x6
    local x8 = x7 + x7
    local x9 = x8 + x8
    local x10 = x9 + x9
    local x11 = x10 + x10
    local x12 = x11 + x11
    local x13 = x12 + x12
    local x14 = x13 + x13
    local x15 = x14 + x14
    local x16 = x15 + x15
    local x17 = x16 + x16
    local x18 = x17 + x17
    local x19 = x18 + x18
    local x20 = x19 + x19
    local x21 = x20 + x20
    local x22 = x21 + x21
    local x23 = x22 + x22
    local x24 = x23 + x23
    return x24
end

assert(run() == 50331648)

local additions = 0
local mt = {}
mt.__add = function(left, right)
    additions = additions + 1
    return setmetatable({ value = left.value + right.value }, mt)
end
return_dag_source = setmetatable({ value = 3 }, mt)
assert(run().value == 50331648)
assert(additions == 24, "shared definitions must execute once")
print("regress_510_return_lookup_value_dag", additions)

-- 两个独立 seed 启用私有字段分析；未知访问链只查询一次，不能在值域兜底中指数重扫。
-- unluac: expect-contains [[.child.child.child.child.child.child.child.child]]
local function lookup_chain(input)
    local first = {}
    local second = {}
    first.value = input.child.child.child.child.child.child.child.child.child.child.child.child.child.child.child.child.child.child.child.child.child.child.child.child.child.child.child.child.child.child.child.child
    return first, second
end
local reads = 0
local node = setmetatable({}, {__index = function(self, key)
    assert(key == "child")
    reads = reads + 1
    return self
end})
local first, second = lookup_chain(node)
assert(first.value == node and next(second) == nil and reads == 32)
node.child = node
first, second = lookup_chain(node)
assert(first.value == node and next(second) == nil and reads == 32)
print("private-field-chain", reads)
