local function build_report(seed: number, items: { number }): string
    local acc: number = seed
    local marks = {}

    for index, value in ipairs(items) do
        if value % 3 == 0 then
            acc += index
            continue
        end

        local delta = if value > index then value - index else index - value
        acc += delta
        marks[#marks + 1] = `#{index}:{acc}`
    end

    return `seed={seed} acc={acc} marks={table.concat(marks, ",")}`
end

print("luau-continue", build_report(5, { 4, 6, 9, 7, 12, 15, 3, 11 }))
