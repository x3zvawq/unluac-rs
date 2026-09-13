-- 互斥同形读取合并保留全部原 GETTABLE 来源；不同 scratch 槽不能借一支许可。
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[if p1_0 then]]
-- unluac: expect-contains [[if p2_0 then]]
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
