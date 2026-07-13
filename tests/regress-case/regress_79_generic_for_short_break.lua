-- regress_79_generic_for_short_break#1: short-circuit headers are not loop continuations
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b)
    local x = 0
    for _, _ in pairs({ 1, 2 }) do
        print("regress_79_generic_for_short_break#1 body", x)
        if a and b then
            break
        end
    end
    return x
end

print("regress_79_generic_for_short_break#1", run(true, true))
