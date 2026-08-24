-- regress_92_repeat_single_condition_and_generic_break#1: one-node repeat condition must survive early continue/break
-- regress_92_repeat_single_condition_and_generic_break#2: generic-for body==exit means immediate break, not empty body
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[in function()]]
local function repeat_single_condition(a, xs)
    repeat
        if a then
            if xs[0] then
                break
            end
            continue
        end
    until a
    return 1
end

local function generic_immediate_break()
    local calls = 0
    local function iter()
        calls = calls + 1
        if calls == 1 then
            return calls
        end
    end
    for _ in iter do
        break
    end
    return calls
end

local function repeat_prefix_continue()
    local rounds = 0
    local probes = 0
    local function probe(value)
        probes = probes + 1
        return value
    end
    repeat
        rounds = rounds + 1
        if rounds == 1 then
            continue
        end
        if probe(false) then
            continue
        end
        if probe(true) then
            break
        end
    until rounds > 3
    return rounds, probes
end

print(
    "regress_92_repeat_single_condition_and_generic_break#1",
    repeat_single_condition(true, { [0] = false })
)
print(
    "regress_92_repeat_single_condition_and_generic_break#2",
    generic_immediate_break()
)
print(
    "regress_92_repeat_single_condition_and_generic_break#3",
    repeat_prefix_continue()
)
