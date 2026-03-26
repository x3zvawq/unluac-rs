local function decorate(tag: string, value: number): string
    local parity = if value % 2 == 0 then "even" else "odd"
    local body = `{tag}:{parity}:{value}`
    return `[{body}] len={#body} brace=\{}`
end

local pieces = {}

for i = 1, 5 do
    if i == 2 then
        continue
    end

    pieces[#pieces + 1] = decorate(`item-{i}`, i * i - 1)
end

print("luau-interp", table.concat(pieces, "|"))
