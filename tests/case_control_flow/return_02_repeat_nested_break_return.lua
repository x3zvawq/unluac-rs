-- regress_157_repeat_nested_break_return#1: 嵌套break/return不把repeat本轮单臂推成跨loop if-else
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[ = 4]]
local function run(a, b, c, d)
    local i = 0
    repeat
        i = i + 1
        if a then
            if b then
                break
            elseif c then
                return i
            end
        end
    until (d and i >= 3) or i >= 4
    return i
end

local until_three = run(false, false, false, true)
local broken = run(true, true, false, false)
local returned = run(true, false, true, false)
local until_four = run(false, false, false, false)
assert(until_three == 3 and broken == 1 and returned == 1 and until_four == 4)
print("regress_157_repeat_nested_break_return#1", until_three)
print("regress_157_repeat_nested_break_return#2", broken)
print("regress_157_repeat_nested_break_return#3", returned)
print("regress_157_repeat_nested_break_return#4", until_four)
