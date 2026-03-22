local function generic_for_mutator(list)
    local sum = 0

    for index, value in ipairs(list) do
        local a, b, c = index, value, list[index]
        sum = sum + a + b + c

        if sum > 20 then
            return a, b, c, sum
        end
    end

    return sum
end

print("gfor-mut", generic_for_mutator({ 3, 4, 5, 6 }))
