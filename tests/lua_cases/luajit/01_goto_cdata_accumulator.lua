local total = 0LL
local i = 0LL

::loop::
i = i + 1LL

if i > 10LL then
    print("luajit-cdata-goto", tostring(total), tostring(i))
    return
end

if (tonumber(i) % 3) == 0 then
    total = total + i * 2LL
    goto loop
end

total = total + i + 5LL
goto loop
