-- entry-nil 共享图在嵌套循环前后保留相同的 nil 证明，不能吞掉可观察读取或非 nil 清零。
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function choose(outer, a, b, probe)
    local x
    if outer then
        for i0 = 1, 1 do
            for i1 = 1, 1 do
                for i2 = 1, 1 do
                    for i3 = 1, 1 do
                        for i4 = 1, 1 do
                            for i5 = 1, 1 do
                                for i6 = 1, 1 do
                                    for i7 = 1, 1 do
                                        local unused = probe.value
                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
        if a then
            local unused = probe.value
            if b then
                x = 1
            end
        end
    else
        x = 2
    end
    return x
end

local reads = 0
local probe = setmetatable({}, {
    __index = function()
        reads = reads + 1
        return 7
    end,
})
local value = choose(true, true, false, probe)
assert(value == nil)
assert(reads == 2)

-- 同一个 entry-nil result 在路径内已经写成非 nil 后，最终清空不是冗余边 copy。
local observed
local ticks = 0
local function tick()
    ticks = ticks + 1
end
local function write_then_clear(flag, candidate)
    local result
    if flag then
        result = candidate
        tick()
        observed = result
        result = nil
    end
    return result
end

local token = {}
assert(write_then_clear(true, token) == nil)
assert(write_then_clear(false, token) == nil)
assert(observed == token)
assert(ticks == 1)

local weak = setmetatable({}, { __mode = "v" })
local cleared = false
local function clear_for_gc(flag)
    local result
    if flag then
        result = {}
        weak[1] = result
        collectgarbage("collect")
        result = nil
        collectgarbage("collect")
        cleared = weak[1] == nil
    end
end

clear_for_gc(true)
assert(cleared)
print("regress_553_entry_nil_nested_flow", value, reads, observed == token, ticks, cleared)
