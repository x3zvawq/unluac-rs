-- 两条原路径即使读取相同字段，也须保留各自的条件检查，不能变成 Boolean 中转链。
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[if p1_0 then]] [[@debug=stripped]]
-- unluac: expect-contains [[if p2_0 then]] [[@debug=stripped]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=2]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]] [[@debug=stripped]]
-- unluac: expect-not-contains [[not not]]
-- unluac: expect-ast-count [[repeat]] [[2]]
-- unluac: expect-contains [[local padding = 0]] [[@debug=retained]]
local function matching(flag, box)
    repeat
        if flag then
            if box.value then break end
        else
            if box.value then break end
        end
    until true
end

local function distinct(flag, box)
    repeat
        if flag then
            -- O0 保留 r2 的准备，原读取写 r3；另一支读取写 r2。
            local padding = 0
            if box.value then break end
        else
            if box.value then break end
        end
    until true
end

local reads = 0
local expected = false
local box = setmetatable({}, {
    __index = function(_, key)
        reads = reads + 1
        assert(key == "value")
        return expected
    end,
})
matching(false, box)
matching(true, box)
distinct(false, box)
distinct(true, box)
expected = true
matching(false, box)
matching(true, box)
distinct(false, box)
distinct(true, box)
assert(reads == 8)
print("alternative-read-events", reads)
