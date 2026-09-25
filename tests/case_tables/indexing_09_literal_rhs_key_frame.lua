-- key 的 CALL/字段读取可改写目标 cell，原目标快照和字面量仍保持各 VM 的时点。
-- unluac: expect-contains [[().field] = true]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=5]] [[@dialect=luajit]]
local target, key_factory
local function write_flag()
    target[key_factory().field] = true
end
local trace = ""
local function observed(name)
    return setmetatable({}, { __newindex = function(_, key, value)
        assert(key == "chosen" and value == true)
        trace = trace .. "store:" .. name
    end })
end
local original = observed("original")
local middle = observed("middle")
local last = observed("last")
key_factory = function()
    trace = trace .. "call;"
    target = middle
    return setmetatable({}, { __index = function(_, key)
        assert(key == "field")
        trace = trace .. "field;"
        target = last
        return "chosen"
    end }), "discarded"
end
target = original
write_flag()
local expected = _VERSION == "Lua 5.1" and "original" or "last"
assert(trace == "call;field;store:" .. expected)
print("indexing_09_literal_rhs_key_frame", trace)
