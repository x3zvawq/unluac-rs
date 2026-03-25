local outer = 0
local inner = 0
local total = 0

while outer < 4 do
    outer = outer + 1
    local j = 0

    while j < 5 do
        j = j + 1
        inner = inner + 1
        total = total + outer + j

        if total > 18 and j > 2 then
            goto done
        end
    end
end

::done::
print("goto-break-like", outer, inner, total)
