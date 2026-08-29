-- Sequential locals become visible one by one; a later metamethod can observe that scope.
-- unluac: expect-not-contains [[local first_single, second_single]]

local function scope_probe(expected, forbidden)
    return setmetatable({}, {
        __index = function()
            local names = {}
            for index = 1, 64 do
                names[(debug.getlocal(2, index)) or false] = true
            end
            return names[expected] == true and (forbidden == nil or names[forbidden] ~= true)
        end,
    })
end

local function run_adjacent()
    local probe = scope_probe("first")
    local first = 41
    local second = probe.value
    return first, first, second, second
end

local function run_single_adjacent()
    local seed = 42
    local saw_gap = false
    local function hook()
        local has_first = false
        local has_second = false
        for index = 1, 64 do
            local name = debug.getlocal(2, index)
            if name == "first_single" then
                has_first = true
            elseif name == "second_single" then
                has_second = true
            end
        end
        if has_first and not has_second then
            saw_gap = true
        end
    end
    debug.sethook(hook, "l")
    local first_single = 41
    local second_single = seed
    debug.sethook()
    return first_single, first_single, second_single, second_single, saw_gap
end

local first_a, first_b, observed_a, observed_b = run_adjacent()
assert(first_a == 41 and first_b == 41)
assert(observed_a == true and observed_b == true)
local first_single_a, first_single_b, second_single_a, second_single_b, saw_gap = run_single_adjacent()
assert(first_single_a == 41 and first_single_b == 41)
assert(second_single_a == 42 and second_single_b == 42 and saw_gap == true)
print("regress341", first_a, first_b, observed_a, observed_b)
