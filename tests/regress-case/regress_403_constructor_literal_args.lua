-- regress_403_constructor_literal_args: eventless literal args may surround a constructor handoff
-- unluac: expect-contains [[("prefix", {]]
-- unluac: expect-contains [[}, 17)]]

local function consume(prefix, value, suffix)
    return prefix, value.get(), suffix
end

local function build()
    local callee = consume
    local value = {}
    value.get = function()
        return 7
    end
    return callee("prefix", value, 17)
end

local prefix, value, suffix = build()
assert(prefix == "prefix", prefix)
assert(value == 7, value)
assert(suffix == 17, suffix)
print("regress_403_constructor_literal_args", prefix, value, suffix)
