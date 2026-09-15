-- FASTCALL direct 参数和普通调用共用依赖链，但保留各自的站点与参数复杂度约束。
local function text(value)
    local result = not value
    result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result
    result = not result
    return tostring(not not result)
end
assert(text(nil) == "false")
assert(text(false) == "false")
assert(text(0) == "true")
assert(text("") == "true")
local function kind(value)
    local result = not value
    result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result
    return type(not not result)
end
assert(kind(0) == "boolean" and kind(nil) == "boolean")
print("regress_551_pure_argument_chain", "OK")
