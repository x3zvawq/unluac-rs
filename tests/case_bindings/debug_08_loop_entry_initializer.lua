-- debug start 位于回边 phi 时，前置块的初始化与循环写回仍共用源码绑定。
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]]
-- unluac: expect-contains [[until (function(]]
-- unluac: expect-contains [[count = value]] [[@debug=retained]]
-- unluac: expect-contains [[return count]] [[@debug=retained]]
local function exercise(warm)
    if warm then print("warm") end
    local count = 0
    repeat
        local value = count + 1
        count = value
    until (function(limit) return value == limit end)(3)
    return count
end
assert(exercise(true) == 3 and exercise(false) == 3)
print("loop-entry-initializer")
