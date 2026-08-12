-- regress_110_luau_generic_for_exit_break_pad#1: generic-for exit 透明 pad 汇入立即 break body
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[                    break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, state, probe, xs)
    local x = 0
    while not state.done do
        repeat
            if a then
                if probe[x] then
                    break
                end
                for k, v in xs do
                    break
                end
            else
                x = x + 1
            end
            break
        until state.done
    end
    return x
end

local calls = 0
local state = { done = false }
local function iterator()
    calls = calls + 1
    if calls <= 2 then
        state.done = true
        return calls, calls
    end
end

local result = run(true, state, {}, iterator)
print("regress_110_luau_generic_for_exit_break_pad#1", result, calls)
assert(result == 0 and calls == 1)
