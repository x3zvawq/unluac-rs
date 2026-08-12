-- regress_311_repeat_exit_parallel_snapshot: repeat 正常退出必须保留并行赋值的 RHS 快照
-- unluac: expect-not-contains [[unluac error]]

local function swap_or_break(stop)
    local left, right = 1, 2
    local count = 0
    repeat
        if stop then
            break
        end
        left, right = right, left
        count = count + 1
    until count >= 1
    return left, right
end

local trace = 0
local function snapshot_across_pad(skip, again, gate)
    local state = 1
    local result = 0
    local function read_state()
        return state
    end
    if not skip then
        while true do
            result = state
            state = state + 1
            if not again then
                if gate then
                    trace = trace + 1
                end
                break
            end
            again = false
        end
    end
    return result, read_state
end

local break_left, break_right = swap_or_break(true)
local swap_left, swap_right = swap_or_break(false)
assert(break_left == 1 and break_right == 2)
assert(swap_left == 2 and swap_right == 1)
local skipped, skipped_state = snapshot_across_pad(true, false, false)
local once, once_state = snapshot_across_pad(false, false, true)
local twice, twice_state = snapshot_across_pad(false, true, false)
assert(skipped == 0 and skipped_state() == 1)
assert(once == 1 and once_state() == 2)
assert(twice == 2 and twice_state() == 3)
assert(trace == 1)
print("regress_311_repeat_exit_parallel_snapshot", "OK")
