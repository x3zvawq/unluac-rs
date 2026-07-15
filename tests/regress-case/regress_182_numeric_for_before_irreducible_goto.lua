-- regress_182_numeric_for_before_irreducible_goto#1: 局部不可规约流不得拖垮前置 numeric-for
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]

local total = 0
for i = 1, 3 do
    total = total + i
end

local x = 0
local y = 0
if x == 0 then
    goto left
end
goto right

::left::
x = x + 1
y = y + 10
if x < 3 then
    goto right
end
goto done

::right::
x = x + 2
y = y + 1
if y < 13 then
    goto left
end

::done::
print("regress_182_numeric_for_before_irreducible_goto#1", total, x, y)
