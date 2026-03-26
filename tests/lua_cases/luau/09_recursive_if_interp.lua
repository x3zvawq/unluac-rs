local function cascade(depth: number, bias: number): number
    return if depth <= 1
        then bias
        else depth + cascade(depth - 1, bias + (if depth % 2 == 0 then 2 else -1))
end

local outputs = {}

for i = 3, 6 do
    outputs[#outputs + 1] = `{i}:{cascade(i, i % 3)}`
end

print("luau-recursive", table.concat(outputs, ","))
