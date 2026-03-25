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
print("goto-irreducible", x, y)
