local funcs = {}

for i = 1, 5 do
    local captured = i * 10
    funcs[#funcs + 1] = function()
        return captured
    end

    if i == 3 then
        break
    end
end

print("break", funcs[1](), funcs[2](), funcs[3](), funcs[4] == nil)
