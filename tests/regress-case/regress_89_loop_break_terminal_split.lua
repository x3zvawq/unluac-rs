-- regress_89_loop_break_terminal_split#1: break exit may split into post-loop and duplicated return
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, xs)
    local x = 0
    for _ in xs do
        if xs[x] then
            break
        end
    end
    while not b do
        if a then
            if xs[x] then
                break
            end
            break
        end
        x = x + 1
    end
    return x
end

print(
    "regress_89_loop_break_terminal_split#1",
    run(true, false, { [0] = true }),
    run(true, false, {}),
    run(false, true, { true })
)
