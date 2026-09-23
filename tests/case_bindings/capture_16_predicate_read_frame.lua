-- 上值比较消费原 GETUPVAL 准备，不为同槽读取留下独立声明；读取仍在元方法写之后。
-- unluac: expect-contains [[if current == 1 then]] [[@debug=retained]]
-- unluac: expect-ast-max [[local-decl]] [[0]] [[@proto=2]]
-- unluac: expect-ast-max [[local-decl]] [[0]] [[@proto=1]] [[@dialect=luajit]]
local current = 0
local writes = {}
local proxy = setmetatable({}, {
    __newindex = function(_, key, value)
        assert(key == "value")
        current = value
        writes[#writes + 1] = value
    end,
})
local function inspect(value)
    proxy.value = value
    if current == 1 then
        return "one"
    end
    return "other"
end
assert(inspect(1) == "one")
assert(inspect(2) == "other")
assert(inspect(1) == "one")
assert(table.concat(writes, ",") == "1,2,1")
print("capture_16_predicate_read_frame", current)
