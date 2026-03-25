local function make_pipeline(seed)
    local bias <const> = seed * 3
    local prefix <const> = "p" .. seed

    local function stage_one(value)
        local adjust <const> = bias + value
        return function(flag)
            if flag then
                return prefix .. ":" .. (adjust + seed)
            end
            return prefix .. ":" .. (adjust - seed)
        end
    end

    return function(values)
        local out = {}
        for i = 1, #values do
            local emit = stage_one(values[i])
            out[#out + 1] = emit(i % 2 == 0)
        end
        return table.concat(out, "|")
    end
end

local run = make_pipeline(4)
print(run({ 1, 2, 3, 4 }))
