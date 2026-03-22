local i = 0

::again::
i = i + 1

if i < 3 then
    goto again
end

print("goto", i)
