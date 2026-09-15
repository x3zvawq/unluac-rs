-- unluac: expect-not-contains [[ == nil]]
-- unluac: expect-contains [[local r1_0 = nil]]
-- unluac: expect-contains [[r2_0 = nil]]

local function discard_literal_equality(value)
    local unused = value == nil
    if 1 == 1 then
        print("discard-literal-equality", value)
    else
        print("unreachable", unused)
    end
end

discard_literal_equality(false)

-- 比较写回必须仍清除同槽的旧弱表根；只删除整个声明会让旧对象活过 GC。
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
