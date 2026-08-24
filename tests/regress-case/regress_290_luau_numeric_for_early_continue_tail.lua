-- regress_290_luau_numeric_for_early_continue_tail: early continue不能吞掉外层共享tail
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[local r1_2]]
-- unluac: expect-contains [[r1_0 = r1_0 + r1_1]]

local function run(a, b, c, n)
    local count = 0
    for j = 1, n do
        if not a then
            print(j)
        elseif b then
            continue
        end
        count = count + j
        if c then
            break
        end
    end
    return count
end

local first = run(false, false, false, 2)
local second = run(true, true, false, 2)
local third = run(true, false, true, 2)
assert(first == 3, first)
assert(second == 0, second)
assert(third == 1, third)
print("regress_290_luau_numeric_for_early_continue_tail", first, second, third)
