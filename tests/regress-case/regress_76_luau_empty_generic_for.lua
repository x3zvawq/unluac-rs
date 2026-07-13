-- regress_76_luau_empty_generic_for#1: Luau folds a continue-only generic-for body into its header
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local function drain(xs)
    local result = 0
    for _ in xs do
        repeat
            for _ in xs do
                continue
            end
        until result < 3
    end
    return result
end

print("regress_76_luau_empty_generic_for#1", drain({ 1, 2, 3 }))
