-- regress_24_branch_shared_continuation#1: branch arms share a non-terminal continuation
-- unluac: expect-contains [[return "early"]]
-- unluac: expect-contains [[":tail"]]
-- unluac: expect-contains [[if p1_0 and not (p1_1 or p1_2) then]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local function branch_shared_continuation(a, b, c, d)
    local result = "start"
    if a and not b and not c then
        if d then
            return "early"
        end
        result = result .. ":body"
    end
    result = result .. ":tail"
    return result
end

print("regress_24_branch_shared_continuation#1", branch_shared_continuation(true, false, false, false))
