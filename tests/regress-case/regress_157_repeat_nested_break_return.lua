-- regress_157_repeat_nested_break_return#1: 嵌套break/return不把repeat本轮单臂推成跨loop if-else
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
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

print("regress_157_repeat_nested_break_return#1", run(false, false, false, true))
print("regress_157_repeat_nested_break_return#2", run(true, true, false, false))
print("regress_157_repeat_nested_break_return#3", run(true, false, true, false))
print("regress_157_repeat_nested_break_return#4", run(false, false, false, false))
