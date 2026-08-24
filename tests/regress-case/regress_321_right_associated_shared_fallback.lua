-- unluac: expect-contains [[p1_0 and (p1_1 or p1_2) or not p1_1 and p1_2]]

local function choose(guard, left, fallback)
    return (guard and (left or fallback)) or ((not left) and fallback)
end

print("regress_321_right_associated_shared_fallback", choose(true, false, "fallback"), choose(false, "left", false))
