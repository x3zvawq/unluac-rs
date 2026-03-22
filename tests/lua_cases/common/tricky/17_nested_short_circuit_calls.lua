local function run_case(first)
    local log = {}

    local function step(name, value)
        log[#log + 1] = name
        return value
    end

    local result = (step("a", first) and (step("b", false) or step("c", "fallback")) and step("d", 8))
        or step("e", 13)

    return result, table.concat(log, ",")
end

local result1, log1 = run_case(true)
local result2, log2 = run_case(false)

print("short-call", result1, log1)
print("short-call", result2, log2)
