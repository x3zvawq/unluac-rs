-- Sequential locals become visible one by one; a later metamethod can observe that scope.

local function scope_probe(expected)
    return setmetatable({}, {
        __index = function()
            local names = {}
            for index = 1, 64 do
                names[(debug.getlocal(2, index)) or false] = true
            end
            return names[expected] == true
        end,
    })
end

local function run_adjacent()
    local probe = scope_probe("first")
    local first = 41
    local second = probe.value
    return first, first, second, second
end

local first_a, first_b, observed_a, observed_b = run_adjacent()
assert(first_a == 41 and first_b == 41)
assert(observed_a == true and observed_b == true)
print("regress341", first_a, first_b, observed_a, observed_b)
