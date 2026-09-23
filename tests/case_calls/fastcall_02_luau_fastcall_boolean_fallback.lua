-- FASTCALL1 在参数求值之后读取 fallback；__index 可在此期间替换全局 assert。
-- Boolean AND 的入口 false 写与原结果槽配对，不能因 header 的逻辑引用消失就单删。
-- unluac: expect-ast-count [[local-binding]] [[5]] [[@proto=0]]
-- unluac: expect-not-contains [[ = print]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
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
-- O0 的普通 CALL 在参数之前读取 callee；优化档的 FASTCALL fallback 在参数之后读取。
-- runner 按同一优化档精确比较整条输出轨迹，不能用另一档的合法轨迹替代当前结果。
local observed = table.concat(trace, ",")
saved_assert(observed == "index1,index2" or observed == "index1,index2,changed:true")
print("regress_585_luau_fastcall_boolean_fallback", observed)
