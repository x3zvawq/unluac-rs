-- regress_86_numeric_for_duplicated_return_state#1: duplicated return exits keep one outer state
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, xs)
    local x = 0
    if a then
        for _ = 1, 3 do
            while not b do
                for _ in xs do
                    x = x + 1
                    x = x + 1
                    x = x + 1
                end
                if a then
                    continue
                end
            end
            continue
        end
    else
        for _ in xs do
            print("regress_86_numeric_for_duplicated_return_state#1 body", x)
        end
    end
    return x
end

print(
    "regress_86_numeric_for_duplicated_return_state#1",
    run(true, true, { true }),
    run(false, true, { true })
)
