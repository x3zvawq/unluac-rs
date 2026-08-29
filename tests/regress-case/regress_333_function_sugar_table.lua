-- Table-field ordered walker: stable receiver aliases may cross allocation, field prefixes may not.
-- unluac: expect-contains [[:table_relaxed(]]

local method_owner = {}
function method_owner:table_relaxed(value)
    return value
end

local function table_sink(...)
    local receiver_alias = ...
    local values = { receiver_alias.table_relaxed(receiver_alias, 41) }
    return values[1]
end

assert(table_sink(method_owner) == 41)
print("function-sugar-table", table_sink(method_owner))
