local function make_router(flag: boolean, offset: number)
    return function(name: string?, values: { number }): string
        local total: number = 0

        for index, value in ipairs(values) do
            local weight = if flag then index + offset else offset - index
            total += value * weight
        end

        local label = if name then name else "anon"
        local mode = if total > 0 then "pos" elseif total == 0 then "zero" else "neg"
        return `router {label} {mode} {total}`
    end
end

local run_a = make_router(true, 3)
local run_b = make_router(false, 6)

print(run_a("alpha", { 2, 5, 1, 4 }))
print(run_b(nil, { 3, 1, 2 }))
