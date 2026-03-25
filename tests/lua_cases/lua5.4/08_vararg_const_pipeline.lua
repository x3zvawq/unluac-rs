local function pack_sum(tag, ...)
    local prefix <const> = tag
    local values = { ... }
    local total = 0

    for i = 1, #values do
        local current <const> = values[i]
        if i % 2 == 0 then
            total = total + current * i
        else
            total = total + current
        end
    end

    return prefix .. ":" .. total, #values
end

local function forward(...)
    return pack_sum("sum", ...)
end

local first, second = forward(3, 4, 5, 6)
print(first, second)
