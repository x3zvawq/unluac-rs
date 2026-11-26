-- regress_74_degenerate_numeric_for#1: unreachable latch still belongs to a numeric for
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[ = 1, 3 do]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-ast-count [[numeric-for]] [[2]]
-- 直接终止的两臂采用与显式 else 相同的正向条件，避免回编译轮次交替反转。

for _ = 1, 3 do
    break
end

print("regress_74_degenerate_numeric_for#1")

local function terminal_body(flag)
    for index = 1, 3 do
        if flag then
            break
        end
        return index
    end
    return 0
end

local immediate = terminal_body(true)
local returned = terminal_body(false)
assert(immediate == 0 and returned == 1)
assert(terminal_body(nil) == 1)
assert(terminal_body(0) == 0)
assert(terminal_body("") == 0)
print("regress_74_degenerate_numeric_for#2", immediate, returned)
