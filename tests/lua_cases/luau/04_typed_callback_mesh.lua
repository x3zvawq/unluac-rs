local function simulate(
    seed: number,
    values: { number },
    step: (number, number, number) -> number
): string
    local history = {}
    local acc: number = seed

    for index, value in ipairs(values) do
        acc = step(acc, value, index)
        history[#history + 1] = acc
    end

    return `sim {table.concat(history, ",")} final={acc}`
end

local report = simulate(4, { 3, 9, 2, 8, 5 }, function(acc: number, value: number, index: number): number
    local next_value = if index % 2 == 0 then acc + value else acc - value + index
    return next_value
end)

print(report)
