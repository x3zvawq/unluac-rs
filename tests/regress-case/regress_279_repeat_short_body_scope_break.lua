-- regress_279_repeat_short_body_scope_break#1: repeat 的短路 body 臂可先进入内层 loop，再 break 外层
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

print(
    "regress_279_repeat_short_body_scope_break#1",
    run(true, false, false, { [3] = true }),
    run(true, true, false, {}),
    run(false, false, true, { [2] = true })
)
