-- Constructor run facts must preserve non-call returns and later callee starts.
-- 八个返回构造器和独立 callee 快照保持各自边界，不增添调用准备中转。
-- unluac: expect-ast-count [[function]] [[14]]
-- unluac: expect-ast-count [[table-constructor]] [[11]]
-- unluac: expect-ast-max [[local-binding]] [[19]]
-- unluac: expect-ast-max [[local-binding]] [[5]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=luau]] [[@debug=stripped]]
local function objects()
    local a = { read = function() return 1 end }
    local b = { read = function() return 2 end }
    local c = { read = function() return 3 end }
    local d = { read = function() return 4 end }
    local e = { read = function() return 5 end }
    local f = { read = function() return 6 end }
    local g = { read = function() return 7 end }
    local h = { read = function() return 8 end }
    return a, b, c, d, e, f, g, h
end

function __reg554_collect(...)
    local total = 0
    for i = 1, select("#", ...) do
        total = total + select(i, ...).read()
    end
    return total
end

local function later_callee()
    local prefix = { read = function() return 17 end }
    local callee = __reg554_collect
    local a = { read = function() return 3 end }
    local b = { read = function() return 5 end }
    return callee(a, b), prefix.read()
end

assert(__reg554_collect(objects()) == 36)
local result, prefix = later_callee()
assert(result == 8 and prefix == 17)
-- 求和不能识别返回顺序变化；逐项检查同时覆盖完整的八结果返回。
assert(select("#", objects()) == 8)
for index = 1, 8 do
    assert(select(index, objects()).read() == index)
end
assert(select("#", later_callee()) == 2)
print("regress_554_constructor_run_boundaries", result, prefix)
