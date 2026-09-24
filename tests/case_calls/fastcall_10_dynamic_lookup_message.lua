-- 动态索引先取得首参数快照，消息转换随后改写同一键，不可重读或调换求值顺序。
-- unluac: expect-not-contains [[unluac error]]
-- 五个源码绑定足够；检查函数和元方法不需要额外参数中转。
-- unluac: expect-ast-count [[local-binding]] [[5]]
local function check(values, key)
    assert(values[key], "check:" .. tostring(key))
end

local trace = ""
local values = setmetatable({}, {
    __index = function()
        trace = trace .. "lookup;"
        return true
    end,
})
local key = setmetatable({}, {
    __tostring = function(self)
        trace = trace .. "message;"
        values[self] = false
        return "key"
    end,
})
local calls = { check }
calls[1](values, key)
assert(values[key] == false and trace == "lookup;message;")
print("fastcall-dynamic-lookup-message", trace)
