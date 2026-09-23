-- numeric-for 迭代的尾部机械块不延长 debug binding 到下一轮，也不吞掉原始比较。
-- unluac: expect-ast-count [[do-block]] [[0]]
-- unluac: expect-contains [[item == 1 or item == 2]]
local observations = {}

local function inspect(phase, expected, value)
    local found = false
    for slot = 1, 32 do
        local name = debug.getlocal(2, slot)
        if name == "item" then
            found = true
        end
    end
    assert(found == expected, phase)
    observations[#observations + 1] = phase
    return value
end

local function run()
    for index = 1, 2 do
        local item = inspect("before", false, index)
        if item == 1 or item == 2 then
            inspect("body", true, item)
        end
    end
    inspect("after", false, 0)
end

run()
assert(table.concat(observations, ",") == "before,body,before,body,after")
print("debug_07_numeric_for_scope", table.concat(observations, ","))
