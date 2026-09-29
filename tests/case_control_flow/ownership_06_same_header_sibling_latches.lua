-- regress_135_same_header_sibling_latches#1: 单个循环的 sibling latch 不能误拆成嵌套 loop
-- unluac: expect-contains [[while true do]]
-- unluac: expect-not-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
local function run(a, c)
    local x = 0
    while true do
        if a then
            if c then
                break
            end
            x = x + 1
        else
            x = x + 10
        end
    end
    return x
end

local result = run(true, true)
assert(result == 0)
-- 参数在循环内不变；只有两者都为真值的输入会终止。
assert(run(0, "") == 0)
assert(run("", 0) == 0)
assert(run({}, true) == 0)
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=1]]
print("regress_135_same_header_sibling_latches#1", result)
