-- regress_266_branch_exit_prefix_effect: branch-exit快捷路径不能吞掉未进入条件的可观察读取
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
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
print("regress_266_branch_exit_prefix_effect", value, reads)
