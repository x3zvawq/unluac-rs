-- 完整 CALL 参数帧消费短路结果的前一 COPY 版本，右臂的比较仍只在选中路径执行。
-- unluac: expect-contains [[print("copy-and",]]
-- unluac: expect-contains [[print("copy-or",]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-ast-max [[local-binding]] [[5]]
local function report(subject, left, right)
    print("copy-and", subject and left ~= right)
    print("copy-or", subject or left == right)
end

local comparisons = 0
local meta = {
    __eq = function(left, right)
        comparisons = comparisons + 1
        return left.value == right.value
    end,
}
local left = setmetatable({ value = 1 }, meta)
local right = setmetatable({ value = 2 }, meta)
report(false, left, right)
assert(comparisons == 1)
report(true, left, right)
assert(comparisons == 2)
report("kept", left, right)
assert(comparisons == 3)
report(nil, left, right)
assert(comparisons == 4)
print("comparisons", comparisons)
report(0, left, right)
assert(comparisons == 5)
report("", left, right)
assert(comparisons == 6)
-- 复用对象但改变字段，比较必须读取本次版本；两条 print 的输出仍独立比较。
right.value = 1
report(false, left, right)
assert(comparisons == 7)
report(true, left, right)
assert(comparisons == 8)
report(nil, left, right)
assert(comparisons == 9)
assert(select("#", report(false, left, right)) == 0)
assert(comparisons == 10)
report(true, 7, 7)
assert(comparisons == 10)
