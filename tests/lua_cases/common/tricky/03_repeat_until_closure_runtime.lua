local function repeat_until_nightmare()
    local funcs = {}
    local i = 0

    repeat
        i = i + 1
        local captured_var = i * 2

        funcs[i] = function()
            return captured_var + i
        end

        if captured_var > 10 and i % 2 == 0 then
            break
        end
    until captured_var > 15

    return funcs
end

local funcs = repeat_until_nightmare()
print("repeat-closure", funcs[1](), funcs[3](), funcs[6](), funcs[7] == nil)
