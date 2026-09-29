-- 原比较和原槽覆盖都需要保留，不能用 nil 写代替比较。
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-count [[if]] [[2]]
-- unluac: expect-ast-max [[local-binding]] [[9]]
-- unluac: expect-count [[ == nil]] [[2]]
-- unluac: expect-count [[if 1 == 1 then]] [[2]]

local function discard_literal_equality(value)
    local unused = value == nil
    if 1 == 1 then
        print("discard-literal-equality", value)
    else
        print("unreachable", unused)
    end
end

discard_literal_equality(false)

-- 比较写回必须仍清除同槽的旧弱表根；删除声明或把结果留到更高槽会改变 GC 观察。
local function clear_old_root(weak, value)
    do
        local old = {}
        weak[old] = true
    end
    local unused = value == nil
    if 1 == 1 then
        collectgarbage("collect")
        return not next(weak)
    else
        print(unused)
    end
end
assert(clear_old_root(setmetatable({}, { __mode = "k" }), false))
assert(clear_old_root(setmetatable({}, { __mode = "k" }), nil))

-- 原常量分支仍调用 print 一次，携带原值；无显式 return 保持零结果。
local original_print = print
local observations = 0
local expected
print = function(label, ...)
    observations = observations + 1
    assert(label == "discard-literal-equality" and select("#", ...) == 1)
    assert((...) == expected)
end
expected = nil
assert(select("#", discard_literal_equality(nil)) == 0)
expected = false
assert(select("#", discard_literal_equality(false)) == 0)
expected = 0
assert(select("#", discard_literal_equality(0)) == 0)
expected = ""
assert(select("#", discard_literal_equality("")) == 0)
assert(observations == 4)
print = original_print
assert(print == original_print)

-- 重复使用同一弱表，确认旧根被清空，返回仍是单个 Boolean。
local weak = setmetatable({}, { __mode = "k" })
assert(clear_old_root(weak, 0))
assert(not next(weak))
assert(select("#", clear_old_root(weak, "")) == 1)
assert(not next(weak))
