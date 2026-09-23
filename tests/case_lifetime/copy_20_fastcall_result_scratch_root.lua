-- O2 展开函数中的 FASTCALL fallback 结果留在高槽，低 COPY 只承接比较值。
-- 观察器替换 type 进入 fallback，验证原高结果根、短路顺序以及内联调用必须消失。
-- 显式 collectgarbage 调用会缩短当前栈顶；连续分配改用 VM 自动 GC，保留原 scratch。
-- 源码恢复共用函数体；NOT 操作总量改在原始与每轮回编译字节码中核对。
-- unluac: expect-count [[not ]] [[11]]
-- unluac: expect-instruction-count [[not]] [[31]]
-- unluac: expect-ast-count [[assign]] [[8]] [[@proto=1]]
-- unluac: expect-contains [[--!optimize 2]]
-- unluac: expect-not-contains [[= print]]
-- unluac-runtime: local run = ...
-- unluac-runtime: local check, report = assert, print
-- unluac-runtime: local collect = collectgarbage
-- unluac-runtime: local weak = setmetatable({}, {__mode = "v"})
-- unluac-runtime: local env = setmetatable({}, {__index = getfenv(run)})
-- unluac-runtime: env.assert = function() end
-- unluac-runtime: local second, calls = false, 0
-- unluac-runtime: env.type = function()
-- unluac-runtime:     calls = calls + 1
-- unluac-runtime:     local params, vararg = debug.info(2, "a")
-- unluac-runtime:     check(params == 0 and vararg, "expanded call gained a runtime helper frame")
-- unluac-runtime:     if second and calls == 1 then return "boolean" end
-- unluac-runtime:     local value = {}; weak[1] = value; return value
-- unluac-runtime: end
-- unluac-runtime: local remaining = 10000
-- unluac-runtime: local explicit = false
-- unluac-runtime: env.print = function()
-- unluac-runtime:     local trash
-- unluac-runtime:     if explicit then collect("collect")
-- unluac-runtime:     else repeat trash = {}; remaining = remaining - 1 until remaining == 0 end
-- unluac-runtime:     local alive = weak[1]
-- unluac-runtime:     check((alive ~= nil) == not explicit, "source result root lifetime changed")
-- unluac-runtime:     check(calls == (second and 2 or 1), "wrong short-circuit path")
-- unluac-runtime:     report("scratch root", second, explicit, alive ~= nil)
-- unluac-runtime:     local a,b,c,d,e,f,g,h = false,false,false,false,false,false,false,false
-- unluac-runtime:     return a,b,c,d,e,f,g,h
-- unluac-runtime: end
-- unluac-runtime: setfenv(run, env)
-- unluac-runtime: for path = 1, 2 do
-- unluac-runtime:     second = path == 2
-- unluac-runtime:     explicit, calls, remaining = false, 0, 10000
-- unluac-runtime:     collect("collect")
-- unluac-runtime:     run()
-- unluac-runtime:     explicit, calls = true, 0
-- unluac-runtime:     run()
-- unluac-runtime: end
local function kind(value)
    local result = not value
    result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result
    return (type(not not result))
end
assert(kind(0) == "boolean" and kind(nil) == "boolean")
print("fastcall_result_scratch_root", "OK")
