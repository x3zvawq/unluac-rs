-- 无读取的结果仍来自原 NOT/比较，不能将其初始化或分支写回统一替换成 nil。
-- unluac: expect-ast-count [[function]] [[7]]
-- unluac: expect-ast-max [[local-binding]] [[20]]
-- unluac: expect-not-contains [[ = nil]]
-- unluac: expect-count [[not ]] [[1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=3]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=3]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=4]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=4]]
-- unluac: expect-name [[local:0]] [[discarded]] [[@proto=3]] [[@debug=retained]]
-- unluac: expect-name [[local:0]] [[discarded]] [[@proto=4]] [[@debug=retained]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=5]] [[@debug=retained]]
-- unluac: expect-name [[local:0]] [[truth]] [[@proto=5]] [[@debug=retained]]
-- unluac: expect-name [[local:1]] [[falsity]] [[@proto=5]] [[@debug=retained]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=6]]
-- unluac: expect-name [[local:0]] [[discarded]] [[@proto=6]] [[@debug=retained]]
local check, report, make, count, protect = assert, print, setmetatable, select, pcall
local reads = 0
local comparisons = 0
local _ENV = setmetatable({}, {__index = function()
    reads = reads + 1
    return 7
end})
local function unused_not(value)
    local discarded = not value
    return missing
end
local function unused_comparison(value)
    local discarded = value == nil
    return missing
end
local function unused_order(left, right)
    local discarded = left < right
    return missing
end
local function separate_scopes(value)
    if value == nil then
        local truth = true
    else
        local falsity = false
    end
    return 7
end
local function unused_tail(left, right)
    local discarded = left < right
end
check(unused_not(false) == 7)
check(unused_not(true) == 7)
check(unused_comparison(nil) == 7)
check(unused_comparison(false) == 7)
local object = make({}, {__lt = function()
    check(reads == 4 + comparisons)
    comparisons = comparisons + 1
    return comparisons == 1
end})
check(unused_order(object, object) == 7)
check(unused_order(object, object) == 7)
check(separate_scopes(nil) == 7)
check(separate_scopes(false) == 7)
check(unused_tail(object, object) == nil)
check(reads == 6 and comparisons == 3)
report("unused_initializers", reads, comparisons)

-- 结果未读取也不能丢弃初始化；错误必须发生在后续环境读取之前。
check(unused_not(0) == 7)
check(unused_not("") == 7)
check(unused_not(nil) == 7)
check(unused_comparison(0) == 7)
check(unused_comparison("") == 7)
check(unused_comparison(object) == 7)
check(reads == 12 and comparisons == 3)
check(unused_order(1, 2) == 7)
check(unused_order(2, 1) == 7)
check(unused_order(1, 1) == 7)
check(unused_order(0 / 0, 1) == 7)
check(reads == 16 and comparisons == 3)
check(protect(unused_order, 1, {}) == false)
check(protect(unused_tail, 1, {}) == false)
check(reads == 16 and comparisons == 3)
check(count("#", unused_tail(1, 2)) == 0)
check(count("#", unused_not(false)) == 1)
check(count("#", unused_comparison(nil)) == 1)
check(count("#", unused_order(2, 1)) == 1)
check(count("#", separate_scopes(0)) == 1)
check(separate_scopes("") == 7)
check(reads == 19 and comparisons == 3)
report("unused_initializers_extended", reads, comparisons)
