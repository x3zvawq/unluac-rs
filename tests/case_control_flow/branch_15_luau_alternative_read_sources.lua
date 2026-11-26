-- 两条原路径即使读取相同字段，也须保留各自的条件检查，不能变成 Boolean 中转链。
-- unluac: expect-not-contains [[not not]]
-- unluac: expect-ast-count [[repeat]] [[2]]
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
