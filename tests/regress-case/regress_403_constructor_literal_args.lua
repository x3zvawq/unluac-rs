-- regress_403_constructor_literal_args: stable context args may surround a constructor handoff
-- Empty-table preallocation keeps the installed field separate; context args retain their positions.
-- unluac: expect-contains [[(p2_0,]]
-- unluac: expect-contains [[, 17)]]

local function consume(prefix, value, suffix)
    return prefix, value.get(), suffix
end

local function build(prefix_value)
    local callee = consume
    local value = {}
    value.get = function()
        return 7
    end
    return callee(prefix_value, value, 17)
end

local prefix, value, suffix = build("prefix")
assert(prefix == "prefix", prefix)
assert(value == 7, value)
assert(suffix == 17, suffix)
print("regress_403_constructor_literal_args", prefix, value, suffix)
