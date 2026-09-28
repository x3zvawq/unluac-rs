-- 共享入口的内层所有退出先汇入外层短路尾条件，而不是直接进入其末叶。
-- unluac: expect-ast-min [[repeat]] [[2]] [[@dialect=luau]] [[@proto=1]]
-- unluac: expect-ast-max [[goto]] [[0]] [[@dialect=luau]]
-- unluac: expect-contains [[local step, x = 0, 0]] [[@debug=retained]]
-- unluac: expect-contains [[return step, x]] [[@debug=retained]]
-- unluac: expect-contains [[local b = math.floor(mask / 2) % 2 == 1]] [[@debug=retained]]
-- unluac: expect-contains [[local c = math.floor(mask / 4) % 2 == 1]] [[@debug=retained]]
-- unluac: expect-contains [[local step, x = run(a, b, c, d, xs)]] [[@debug=retained]]
-- unluac: expect-contains [[assert(table.concat(trace, ",") == table.concat(expected, ","))]] [[@debug=retained]]
-- unluac: expect-contains [[print("regress_645#1", mask, step, x, table.concat(trace, ","))]] [[@debug=retained]]
local function run(a, b, c, d, xs)
    local step, x = 0, 0
    while step < 3 do
        step = step + 1
        x = x + 1
        repeat
            repeat
                if b then
                    if c then break else print("regress_645#1", "inner") end
                end
                if d then break end
            until xs[step]
            if a then break end
        until xs[step]
    end
    return step, x
end

local trace = {}
local xs = setmetatable({}, {__index = function(_, key)
    trace[#trace + 1] = key
    return true
end})
for mask = 0, 15 do
    local a = mask % 2 == 1
    local b = math.floor(mask / 2) % 2 == 1
    local c = math.floor(mask / 4) % 2 == 1
    local d = mask >= 8
    trace = {}
    local step, x = run(a, b, c, d, xs)
    local reads_per_step = ((b and c) or d) and 0 or 1
    if not a then reads_per_step = reads_per_step + 1 end
    local expected = {}
    for i = 1, 3 do
        for j = 1, reads_per_step do expected[#expected + 1] = i end
    end
    assert(step == 3 and x == 3)
    assert(table.concat(trace, ",") == table.concat(expected, ","))
    print("regress_645#1", mask, step, x, table.concat(trace, ","))
end


-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]
-- 两臂均汇入外层共享出口；其中一臂提前 return 不应把另一臂误认为 continuation。
local function guarded_alternatives(active, key, editor, stop, nested)
    if active then
        if (key == "back" or key == "escape") and not editor then
            if stop then return "early" end
            if nested then print("guarded alternatives", "nested")
            else print("guarded alternatives", "back") end
        elseif key == "p" or key == "pause" then
            print("guarded alternatives", "pause")
        elseif key == "s" then
            print("guarded alternatives", "sound")
        end
    end
    print("guarded alternatives", "done")
    return "done"
end
assert(guarded_alternatives(false, "back") == "done")
assert(guarded_alternatives(true, "back", false, true) == "early")
assert(guarded_alternatives(true, "escape", false, false, true) == "done")
assert(guarded_alternatives(true, "back") == "done")
assert(guarded_alternatives(true, "back", true) == "done")
assert(guarded_alternatives(true, "pause") == "done")
assert(guarded_alternatives(true, "s") == "done")
assert(guarded_alternatives(true, "other") == "done")
