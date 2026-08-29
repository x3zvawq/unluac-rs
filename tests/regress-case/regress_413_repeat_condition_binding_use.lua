-- regress_413_repeat_condition_binding_use: until shares the repeat body's local scope

local provider = {}

function provider:make()
    return {
        finish = function() end,
    }
end

local function done(value)
    assert(type(value) == "table", "repeat condition lost its body-local binding")
    return true
end

repeat
    local value = provider:make()
    value:finish()
until done(value)

print("regress_413_repeat_condition_binding_use", "OK")
