-- unluac: expect-not-contains [[p1_0 and p1_1 or p1_0 and p1_2]]

local function choose(a, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18)
    return a and b1
        or a and b2
        or a and b3
        or a and b4
        or a and b5
        or a and b6
        or a and b7
        or a and b8
        or a and b9
        or a and b10
        or a and b11
        or a and b12
        or a and b13
        or a and b14
        or a and b15
        or a and b16
        or a and b17
        or a and b18
end

print(
    "regress_425_decision_naturalize_unbounded",
    choose(false, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18),
    choose(true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, 18)
)
