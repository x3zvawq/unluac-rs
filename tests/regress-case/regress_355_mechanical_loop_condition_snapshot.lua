-- regress_355_mechanical_loop_condition_snapshot: mechanical runs must not move snapshots into loop conditions

local function run_while(flag)
    local count = 0
    local first = flag
    local second = not first
    local condition = not second
    if false then
        print(first, second, condition)
    end
    while condition == true do
        count = count + 1
        flag = false
        if count == 2 then
            break
        end
    end
    return count
end

assert(run_while(true) == 2)

repeat_flag = false
repeat_count = 0
local first = repeat_flag
local second = not first
local condition = not second
if false then
    print(first, second, condition)
end
repeat
    repeat_count = repeat_count + 1
    repeat_flag = true
until condition == false or repeat_count == 2
assert(repeat_count == 1)
