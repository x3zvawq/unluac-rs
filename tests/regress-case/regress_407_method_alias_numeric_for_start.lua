-- regress_407_method_alias_numeric_for_start: the numeric-for start is a once-only first event
-- unluac: expect-contains [[:first(), 3 do]]

local owner = {}

function owner:first()
    return 1, 99
end

local observed = {}

local function collect(source)
    local receiver = source
    for value = receiver.first(receiver), 3 do
        observed[#observed + 1] = value
    end
end

collect(owner)
local result = table.concat(observed, ",")
assert(result == "1,2,3", result)
print("regress_407_method_alias_numeric_for_start", result)
