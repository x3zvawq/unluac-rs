-- Debug-hinted source locals remain visible even when they only hand a value to a global.
-- unluac: expect-contains [[local debug_seed =]]

local function caller_has_local(expected)
    local names = {}
    for index = 1, 64 do
        names[(debug.getlocal(2, index)) or false] = true
    end
    return names[expected] == true
end

local function test_debug_seed()
    local debug_seed = { value = 53 }
    global debug_export = debug_seed
    global<const> assert

    assert(caller_has_local("debug_seed"))
    return debug_export.value
end

local function test_debug_scope()
    local function consume(_) end
    local check = assert
    global debug_gate = 0
    global<const> math

    local debug_range = math.max(59, 61)
    consume(debug_range)
    check(caller_has_local("debug_range"))
    return 61
end

print("regress335-debug", test_debug_seed(), test_debug_scope())
