-- regress_411_lua55_global_function_assignment: assignments to declared globals stay assignments
-- unluac: expect-contains [[function direct_target()]]
-- 发布后的低槽局部仍属于后续调用前缀，保留它才能自然恢复两个直接调用。
-- unluac: expect-contains [[forwarded_target = r0_1]] [[@debug=stripped]]
-- unluac: expect-contains [[local function forwarded()]] [[@debug=retained]]
-- unluac: expect-contains [[forwarded_target = forwarded]] [[@debug=retained]]
-- unluac: expect-not-contains [[global function direct_target()]]
-- unluac: expect-not-contains [[global function forwarded_target()]]
-- unluac: expect-not-contains [[= assert]]
-- unluac: expect-ast-max [[local-binding]] [[2]] [[@proto=0]]

global<const> assert, print

global direct_target = 1
direct_target = function()
    return 2
end

global forwarded_target = 3
local forwarded = function()
    return 4
end
forwarded_target = forwarded

assert(direct_target() == 2)
assert(forwarded_target() == 4)

-- 子函数内的普通函数赋值仍继承外层可写声明，不得引入新的 global gate。
local function replace_target()
    function direct_target()
        return 5
    end
end
replace_target()
assert(direct_target() == 5)
print("regress_411_lua55_global_function_assignment")
