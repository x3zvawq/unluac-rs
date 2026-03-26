local function funnel(limit: number): string
    local i: number = 0
    local acc: number = 1
    local seen = {}

    repeat
        i += 1

        if i % 2 == 0 then
            acc += i
            continue
        end

        acc *= i
        seen[#seen + 1] = tostring(acc)
    until i >= limit

    return `repeat {acc} {table.concat(seen, ":")}`
end

print(funnel(7))
