-- Function-sugar guards must preserve nested global lookup semantics and source identities.

self = "global-self"

local nested_object = { value = "receiver" }
nested_object.read_nested_self = function(receiver)
    return function()
        return self, receiver.value
    end
end

local nested_reader = nested_object:read_nested_self()
local nested_self, nested_receiver_value = nested_reader()
assert(nested_self == "global-self")
assert(nested_receiver_value == "receiver")

local function caller_has_local(expected)
    local names = {}
    for index = 1, 64 do
        names[(debug.getlocal(2, index)) or false] = true
    end
    return names[expected] == true
end

local debug_target = { value = 23 }
function debug_target:read_value()
    return self.value
end

-- Policy contracts: retain-debug keeps source local identities even when runtime flow has one use.
local receiver_alias = debug_target
local field_alias = receiver_alias.read_value
assert(field_alias(receiver_alias) == 23)
assert(caller_has_local("receiver_alias"))
assert(caller_has_local("field_alias"))

local forwarded_owner = {}
local forwarded_alias = function()
    return 29
end
forwarded_owner.value = forwarded_alias
assert(forwarded_owner.value() == 29)
assert(caller_has_local("forwarded_alias"))

local chain_owner = {}
function chain_owner:first()
    return {
        finish = function(receiver)
            return receiver.ok
        end,
        ok = true,
    }
end

local chain_value = chain_owner:first()
chain_value:finish()
assert(caller_has_local("chain_value"))

local function identity(value)
    return value
end

local constructor_callee = identity
local constructor_arg = { value = 31 }
local constructor_result, kept_callee, kept_arg =
    constructor_callee(constructor_arg), constructor_callee, constructor_arg
assert(constructor_result.value == 31)
assert(kept_callee == identity and kept_arg == constructor_arg)
assert(caller_has_local("constructor_callee"))
assert(caller_has_local("constructor_arg"))

print("function-sugar-guards", nested_self, constructor_result.value)
