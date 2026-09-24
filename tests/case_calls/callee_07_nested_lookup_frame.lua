-- 嵌套 callee 在原槽逐层读取；参数改写字段后，调用仍使用此前取得的函数。
-- unluac: expect-count [[.nested.field(]] [[1]]
-- unluac: expect-contains [[()) == 23)]]
-- unluac: expect-ast-count [[local-function]] [[2]]
local function invoke(root, argument)
    assert(root.nested.field(argument()) == 23)
end

local events = {}
local leaf = setmetatable({}, {
    __index = function(_, key)
        assert(key == "field")
        events[#events + 1] = "field"
        return function(value)
            events[#events + 1] = "old-call"
            return value
        end
    end,
})
local root = setmetatable({}, {
    __index = function(_, key)
        assert(key == "nested")
        events[#events + 1] = "nested"
        return leaf
    end,
})
local function argument()
    events[#events + 1] = "argument"
    leaf.field = function() error("replacement must not be called") end
    return 23
end
invoke(root, argument)
assert(table.concat(events, ",") == "nested,field,argument,old-call")
print("callee_07_nested_lookup_frame", table.concat(events, ","))
