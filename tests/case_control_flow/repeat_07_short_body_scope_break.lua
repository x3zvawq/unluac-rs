-- regress_279_repeat_short_body_scope_break#1: repeat 的短路 body 臂可先进入内层 loop，再 break 外层
-- unluac: expect-ast-min [[repeat]] [[2]] [[@proto=1]]
-- unluac: expect-ast-min [[break]] [[1]] [[@proto=1]]
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
print(
    "regress_279_repeat_short_body_scope_break#1",
    nested,
    skipped,
    alternate
)
