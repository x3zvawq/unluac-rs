-- regress_279_repeat_short_body_scope_break#1: repeat 的短路 body 臂可先进入内层 loop，再 break 外层
-- unluac: expect-ast-count [[repeat]] [[2]]
-- unluac: expect-ast-count [[break]] [[1]]
-- unluac: expect-ast-count [[if]] [[2]]
-- unluac: expect-ast-count [[local-binding]] [[7]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]] [[@dialect=luau]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=2]] [[@dialect=luau]]
local function run(a, b, c, xs)
    local x = 0
    repeat
        if a or c then
            if not b then
                repeat
                    x = x + 1
                until xs[x]
            end
            break
        end
    until a
    return x
end

local nested = run(true, false, false, { [3] = true })
local skipped = run(true, true, false, {})
local alternate = run(false, false, true, { [2] = true })
assert(nested == 3 and skipped == 0 and alternate == 2)
local reads = 0
local xs = setmetatable({}, {
    __index = function(_, key)
        reads = reads + 1
        assert(key == reads and reads <= 3)
        return key == 3 and 0
    end,
})
assert(run(0, nil, false, xs) == 3)
assert(reads == 3)
reads = 0
assert(run(nil, false, "", xs) == 3)
assert(reads == 3)
reads = 0
assert(run(nil, 0, "", xs) == 0 and reads == 0)
assert(run("", false, nil, {true}) == 1)
-- 直接观察短路返回的值，不能只凭循环退出将数值 0 当成任意 truthy 值。
assert(xs[1] == false and xs[2] == false and xs[3] == 0 and reads == 3)
print(
    "regress_279_repeat_short_body_scope_break#1",
    nested,
    skipped,
    alternate
)
