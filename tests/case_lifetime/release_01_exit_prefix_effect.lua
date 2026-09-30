-- regress_266_branch_exit_prefix_effect: branch-exit快捷路径不能吞掉未进入条件的可观察读取
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[assign]] [[2]] [[@proto=1]]
-- unluac: expect-ast-max [[local-binding]] [[16]]
-- unluac: expect-max-count [[local ]] [[15]]
-- unluac: expect-ast-count [[function]] [[5]]
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=4]]
-- unluac: expect-ast-count [[assign]] [[3]] [[@proto=4]]
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=5]]
-- unluac: expect-ast-count [[assign]] [[4]] [[@proto=5]]
-- unluac: expect-ast-count [[call]] [[3]] [[@proto=5]]
local function choose(outer, a, b, probe)
    local x
    if outer then
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
assert(reads == 1)
assert(choose(true, true, true, probe) == 1)
assert(reads == 2)
assert(choose(true, false, true, probe) == nil)
assert(choose(false, true, true, probe) == 2)
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
        assert(weak[1] ~= nil)
        result = nil
        collectgarbage("collect")
        cleared = weak[1] == nil
    end
end

clear_for_gc(true)
assert(cleared)
print("regress_266_branch_exit_prefix_effect", value, reads, observed == token, ticks, cleared)
cleared = false
clear_for_gc(false)
assert(cleared == false)
