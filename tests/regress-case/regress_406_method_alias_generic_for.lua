-- regress_406_method_alias_generic_for: a sole iterator may atomically consume its receiver alias
-- unluac: expect-contains [[:each() do]]

local owner = { values = { 10, 20 } }

function owner:each()
    return ipairs(self.values)
end

local observed = {}

local function collect_values(source)
    local receiver = source
    for _, value in receiver.each(receiver) do
        observed[#observed + 1] = value
    end
end

collect_values(owner)
local result = table.concat(observed, ",")
assert(result == "10,20", result)
print("regress_406_method_alias_generic_for", result)
