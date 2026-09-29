-- unluac: expect-contains [[p1_0 and (p1_1 or p1_2) or not p1_1 and p1_2]]
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[numeric-for]] [[3]]
-- unluac: expect-ast-max [[local-binding]] [[9]]

local function choose(guard, left, fallback)
    return (guard and (left or fallback)) or ((not left) and fallback)
end

local shared = choose(true, false, "fallback")
local rejected = choose(false, "left", false)
assert(shared == "fallback" and rejected == false)
print("regress_321_right_associated_shared_fallback", shared, rejected)
local values = { false, true, 0, "", {} }
local combinations = 0
for gi = 1, 6 do
    for li = 1, 6 do
        for fi = 1, 6 do
            local expected
            if li == 1 or li == 6 then
                expected = values[fi]
            elseif gi == 1 or gi == 6 then
                expected = false
            else
                expected = values[li]
            end
            assert(choose(values[gi], values[li], values[fi]) == expected)
            combinations = combinations + 1
        end
    end
end
assert(combinations == 216)
assert(select("#", choose(nil, nil, nil)) == 1)
