-- FASTCALL1 在参数求值之后读取 fallback；__index 可在此期间替换全局 assert。
-- Boolean AND 的入口 false 写与原结果槽配对，不能因 header 的逻辑引用消失就单删。
local trace = {}
local saved_assert = assert
local environment = getfenv()
local object = setmetatable({}, {
    __index = function(_, key)
        trace[#trace + 1] = "index" .. key
        environment.assert = function(value)
            trace[#trace + 1] = "changed:" .. tostring(value)
        end
        if key == 1 then
            return "a"
        end
        return "b"
    end,
})

assert(object[1] == "a" and object[2] == "b")
environment.assert = saved_assert
saved_assert(table.concat(trace, ",") == "index1,index2,changed:true")
print("regress_585_luau_fastcall_boolean_fallback", table.concat(trace, ","))
