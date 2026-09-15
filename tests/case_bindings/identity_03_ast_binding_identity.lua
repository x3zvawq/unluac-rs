-- HIR captures and AST-created installer bindings keep separate identities.
-- unluac: expect-not-contains [[(function(]]
-- unluac: expect-ast-count [[function]] [[7]]

local exported = {}
local weak_installers = setmetatable({}, { __mode = "k" })
local captured = assert({ value = 7 })

local function remember_caller(token)
    weak_installers[debug.getinfo(2, "f").func] = true
    return token
end

;(function(token)
    local remembered = remember_caller(token)
    local count = 0
    local function first(delta)
        count = count + delta
        return token, remembered, count, captured.value
    end

    ;(function(suffix)
        local nested_memory = remember_caller(suffix)
        local function nested()
            return token, suffix, nested_memory, captured.value
        end
        exported.nested = nested
    end)("inner")

    exported.first = first
end)("first")

;(function(token)
    local remembered = remember_caller(token)
    local function second()
        return token, remembered, captured.value
    end
    exported.second = second
end)("second")

captured.value = 11
local token, remembered, count, value = exported.first(2)
assert(token == "first" and remembered == "first" and count == 2 and value == 11)
token, remembered, count, value = exported.first(3)
assert(token == "first" and remembered == "first" and count == 5 and value == 11)
token, remembered, value = exported.second()
assert(token == "second" and remembered == "second" and value == 11)
local outer, suffix, nested_memory, nested_value = exported.nested()
assert(outer == "first" and suffix == "inner" and nested_memory == "inner")
assert(nested_value == 11)

-- Exported closures keep their captures, but none captures the installer itself.
collectgarbage("collect")
assert(next(weak_installers) == nil)
print("regress_486_ast_binding_identity", count, value, nested_value)
