-- regress_153_lua55_generic_for_close_break_pad#1: generic-for 的 CLOSE fallthrough 出口保持本轮 break owner
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
local function run(xs, stop)
    local total = 0
    for i, v in ipairs(xs) do
        if v < 0 then
            if i == stop then
                break
            end
        else
            total = total + v
        end
        total = total + 7
    end
    return total
end

local stop_three = run({ 2, 0, -1, 4 }, 3)
local stop_two = run({ 2, 0, -1, 4 }, 2)
assert(stop_three == 16 and stop_two == 34)
assert(run({}, 1) == 0)
assert(run({ -1, 9 }, 1) == 0)
assert(run({ -1, -2 }, false) == 14)
assert(run({ 2, nil, 100 }, 3) == 9)
print(
    "regress_153_lua55_generic_for_close_break_pad#1",
    stop_three,
    stop_two
)
