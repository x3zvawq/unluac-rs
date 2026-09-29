-- binary64 不区分 1 与 1.0 的表示，但原比较不因此变成常量。
-- unluac: expect-contains [[return 1 == 1, 1 < 1.5, 1.5 <= 1]]
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-ast-max [[local-binding]] [[5]]

local function compare()
    assert(2147483647 < 2147483647.5)
    assert(-2147483648 == -2147483648.0)
    assert(-2 < -1.5 and not (-1 <= -1.5))
    assert(0 == -0.0 and -0.0 <= 0 and not (0 < -0.0))

    return 1 == 1.0, 1 < 1.5, 1.5 <= 1
end

local equal, less, greater, extra = compare()
assert(equal == true and less == true and greater == false)
assert(extra == nil)
print("mixed-numeric", equal, less, greater)
