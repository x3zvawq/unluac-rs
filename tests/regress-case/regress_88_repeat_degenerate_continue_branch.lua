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

print(
    "regress_88_repeat_degenerate_continue_branch#1",
    run(false, true, {}),
    run(true, true, { true })
)
