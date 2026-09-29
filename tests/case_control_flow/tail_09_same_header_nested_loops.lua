-- regress_80_same_header_nested_loops#1: Luau shares the numeric-for body header with an inner while
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- 原字节码仍执行 ADD，不能因初始化为常量而删除该运算。
-- unluac: expect-contains [[local r1_0 = 0 + 1]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[6]]
local function run(flag)
    local result = 0
    result = result + 1
    print("regress_80_same_header_nested_loops#1 body", result)
    for _ = 1, 3 do
        while not flag do
            continue
        end
        continue
    end
    return result
end

local result = run(true)
assert(result == 1)
print("regress_80_same_header_nested_loops#1", result)

local saved_print, calls = print, 0
print = function(message, value)
    assert(message == "regress_80_same_header_nested_loops#1 body" and value == 1)
    calls = calls + 1
end
assert(run(0) == 1 and calls == 1)
assert(run("") == 1 and calls == 2)
-- flag 为假时内层只有无副作用的无限回边，这里只运行正常退出路径。
print = saved_print
