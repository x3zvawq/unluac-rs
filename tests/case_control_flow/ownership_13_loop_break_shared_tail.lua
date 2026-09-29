-- regress_280_nested_loop_break_shared_tail#1: active-loop break 与 sibling 路径共享 repeat tail
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[repeat]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=0]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- 末尾 if a then break 可与 until 合成短路条件，但不能根据 while a 消掉检查。
-- unluac: expect-ast-count [[break]] [[1]]
-- unluac: expect-contains [[until p1_0 or p1_3]] [[@dialect=lua5.1]]
-- unluac: expect-contains [[until p1_0 or p1_3]] [[@dialect=lua5.2]]
-- unluac: expect-contains [[until p1_0 or p1_3]] [[@dialect=lua5.3]]
-- unluac: expect-contains [[until p1_0 or p1_3]] [[@dialect=lua5.4]]
-- unluac: expect-contains [[until p1_0 or p1_3]] [[@dialect=lua5.5]]
-- unluac: expect-contains [[until p1_0 or p1_3]] [[@dialect=luau]]
-- unluac: expect-contains [[until p3_0 or p3_3]] [[@dialect=luajit]]
local function run(a, b, c, xs)
    local x = 0
    while a do
        repeat
            if b then
                if c then
                    break
                else
                    print(x)
                end
            end
            if a then
                break
            end
        until xs[x]
    end
    return x
end

local saved_print = print
local visits = 0
local xs = setmetatable({}, {
    __index = function()
        error("truthy a must short-circuit the repeat tail")
    end,
})
assert(run(false, true, false, xs) == 0)
assert(run(nil, true, false, xs) == 0)
-- a 为真时外层循环不终止；观察三次循环体后主动中断，避免用超时作为证明。
print = function(value)
    assert(value == 0)
    visits = visits + 1
    assert(visits < 3, "observed outer loop backedge")
end
assert(not pcall(run, true, true, false, xs))
assert(visits == 3)
visits = 0
assert(not pcall(run, 0, "", nil, xs))
assert(visits == 3)
print = saved_print

print("regress_280_nested_loop_break_shared_tail#1", type(run))
