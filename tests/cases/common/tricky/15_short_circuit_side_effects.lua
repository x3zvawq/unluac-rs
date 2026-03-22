local function run_case(left, right)
    local log = {}

    local function mark(name, value)
        log[#log + 1] = name
        return value
    end

    local result = (mark("a", left) and mark("b", right)) or (mark("c", true) and mark("d", "done"))
    return result, table.concat(log, ",")
end

local result1, log1 = run_case(false, true)
local result2, log2 = run_case(true, 0)

print("short", result1, log1)
print("short", result2, log2)
