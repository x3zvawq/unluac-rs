-- regress_88_repeat_degenerate_continue_branch#1: equal branch targets are the repeat tail, not goto
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, xs)
    local x = 0
    for _ in xs do
        repeat
            if a then
                continue
            end
        until b
        if xs[x] then
            break
        end
    end
    return x
end

local empty_result = run(false, true, {})
local continue_result = run(true, true, { true })
assert(empty_result == 0 and continue_result == 0)
print("regress_88_repeat_degenerate_continue_branch#1", empty_result, continue_result)
