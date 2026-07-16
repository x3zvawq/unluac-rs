-- regress_212_table_constructor_field_order#1: pending integer fields keep binding snapshots
-- regress_212_table_constructor_field_order#2: pending integer fields keep metamethod order
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local value = 20

local function mutate()
    value = 30
    return 10
end

local binding_result = {}
binding_result[2] = value
binding_result[1] = mutate()
print("regress_212_table_constructor_field_order#1", binding_result[1], binding_result[2], value)

local hits = 0
local operand = setmetatable({}, {
    __add = function()
        hits = hits + 1
        return hits
    end,
})

local function mark()
    hits = hits + 10
    return hits
end

local metamethod_result = {}
metamethod_result[2] = operand + 0
metamethod_result[1] = mark()
print("regress_212_table_constructor_field_order#2", metamethod_result[1], metamethod_result[2], hits)
