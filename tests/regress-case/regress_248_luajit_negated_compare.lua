-- regress_248_luajit_negated_compare: ISGE/ISGT 是原关系的逻辑取反
-- unluac: expect-contains [[not]]
-- unluac: expect-not-contains [[unluac error]]

local nan = 0 / 0
assert((nan >= 1) == false)
assert((not (nan < 1)) == true)
assert((nan > 1) == false)
assert((not (nan <= 1)) == true)

local calls = {}
local mt = {
    __lt = function(a, b)
        calls[#calls + 1] = "lt:" .. a.tag .. ":" .. b.tag
        return false
    end,
    __le = function(a, b)
        calls[#calls + 1] = "le:" .. a.tag .. ":" .. b.tag
        return false
    end,
}
local a = setmetatable({ tag = "a" }, mt)
local b = setmetatable({ tag = "b" }, mt)

assert((a >= b) == false)
assert(not (a < b))
assert((a > b) == false)
assert(not (a <= b))
assert(table.concat(calls, ",") == "le:b:a,lt:a:b,lt:b:a,le:a:b")

print("regress_248_luajit_negated_compare")
