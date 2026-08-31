-- regress_373_loop_lookup_eval_count: an __index snapshot must not be reevaluated by a loop header

local reads = 0
local probe = setmetatable({}, {
    __index = function()
        reads = reads + 1
        return true
    end,
})
local first = probe.value
local second = not first
local condition = not second
if false then
    print(first, second, condition)
end
local turns = 0
local function keep_running()
    turns = turns + 1
    return turns < 2
end
while condition == true do
    if not keep_running() then
        break
    end
end
assert(reads == 1)
