local function make_dispatch(prefix: string?)
    local counter: number = 0

    return function(values: { number }): string
        local parts = {}

        for index, value in ipairs(values) do
            if value < 0 then
                counter += -value
                continue
            end

            counter += value
            parts[#parts + 1] = if prefix then `{prefix}-{index}:{counter}` else `slot-{index}:{counter}`
        end

        return table.concat(parts, "|")
    end
end

local dispatch = make_dispatch("luau")
print(dispatch({ 4, -2, 7, 3, -1, 5 }))
