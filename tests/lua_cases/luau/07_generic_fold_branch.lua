local function fold<T>(items: { T }, seed: T, reducer: (T, T, number) -> T): T
    local acc = seed

    for index, item in ipairs(items) do
        acc = reducer(acc, item, index)
    end

    return acc
end

local result = fold({ 5, 2, 9, 1 }, 4, function(acc: number, item: number, index: number): number
    return if index % 2 == 0 then acc + item * index else acc - item + index
end)

print(`luau-generic {result}`)
