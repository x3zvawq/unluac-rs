-- 原比较和原槽覆盖都需要保留，不能用 nil 写代替比较。
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
