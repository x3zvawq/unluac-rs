-- regress_351_extended_call_debug_scope: extended call runs must retain source locals observable through debug.getlocal
-- unluac: expect-contains [[local inspector = inspect_call_scope]]
-- unluac: expect-contains [[local argument = value]]
local observed

local function inspect_call_scope(value)
    local names = {}
    local index = 1
    while true do
        local name = debug.getlocal(2, index)
        if name == nil then
            break
        end
        names[#names + 1] = name
        index = index + 1
    end
    observed = table.concat(names, ",")
    return value
end

local function run_statement(value)
    local inspector = inspect_call_scope
    local argument = value
    inspector(argument)
    return value
end

assert(run_statement(41) == 41)
assert(observed:find("inspector", 1, true) ~= nil)
assert(observed:find("argument", 1, true) ~= nil)

local function run_result(value)
    local inspector = inspect_call_scope
    local argument = value
    local result = inspector(argument)
    return result
end

assert(run_result(42) == 42)
assert(observed:find("inspector", 1, true) ~= nil)
assert(observed:find("argument", 1, true) ~= nil)
