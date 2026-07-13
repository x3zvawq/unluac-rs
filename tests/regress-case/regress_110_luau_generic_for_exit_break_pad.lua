-- regress_110_luau_generic_for_exit_break_pad#1: generic-for exit 透明 pad 汇入立即 break body
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, xs)
    local x = 0
    while not b do
        repeat
            if a then
                if xs[x] then
                    break
                end
                for k, v in xs do
                    break
                end
            else
                x = x + 1
            end
            break
        until b
    end
    return x
end

print("regress_110_luau_generic_for_exit_break_pad#1", run(false, true, {}))
