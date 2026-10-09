-- CALL 后以括号开头的字段/索引左值必须保持独立语句；原来的 nil 写入仍应报错。
local calls = 0
function create(tag, value)
    calls = calls + 1
end
local function field(value)
    local target
    create("field", value)
    target.preserveAspectRatio = value
end
local function index(value, key)
    local target
    create("index", value)
    target[key] = value
end
assert(not pcall(field, 10))
assert(calls == 1)
assert(not pcall(index, 20, "field-name"))
assert(calls == 2)
print("parenthesized-assignment", calls)
