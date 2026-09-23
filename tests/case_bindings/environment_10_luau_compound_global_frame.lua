-- 复合全局写在结果槽覆盖旧值；普通写的操作数 scratch 在写入元方法中仍存活。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[COMPOUND_VALUE += 1]]
-- unluac: expect-contains [[COMPOUND_VALUE -= 2]]
-- unluac: expect-contains [[COMPOUND_VALUE *= 3]]
-- unluac: expect-contains [[COMPOUND_VALUE /= 4]]
-- unluac: expect-contains [[COMPOUND_VALUE %= 5]]
-- unluac: expect-contains [[COMPOUND_VALUE ^= 2]]
-- unluac: expect-contains [[PLAIN_VALUE = PLAIN_VALUE + 1]]
-- unluac: expect-ast-count [[local-binding]] [[0]]
-- unluac-runtime: local run = ...
-- unluac-runtime: local check, report, collect = assert, print, collectgarbage
-- unluac-runtime: local weak = setmetatable({}, {__mode = "v"})
-- unluac-runtime: local events = {}
-- unluac-runtime: local function operation(name, result)
-- unluac-runtime:     return function(left, right)
-- unluac-runtime:         check(left == weak[1])
-- unluac-runtime:         events[#events + 1] = name .. ":" .. right
-- unluac-runtime:         return result
-- unluac-runtime:     end
-- unluac-runtime: end
-- unluac-runtime: local meta = {__add=operation("add",11), __sub=operation("sub",8), __mul=operation("mul",30), __div=operation("div",2.5), __mod=operation("mod",0), __pow=operation("pow",100)}
-- unluac-runtime: local env = setmetatable({}, {
-- unluac-runtime:     __index = function(_, key)
-- unluac-runtime:         check(key == "COMPOUND_VALUE" or key == "PLAIN_VALUE")
-- unluac-runtime:         events[#events + 1] = "read:" .. key
-- unluac-runtime:         local value = setmetatable({}, meta)
-- unluac-runtime:         weak[1] = value
-- unluac-runtime:         return value
-- unluac-runtime:     end,
-- unluac-runtime:     __newindex = function(_, key, value)
-- unluac-runtime:         if value == 10 then check(weak[1] == nil); return end
-- unluac-runtime:         collect("collect")
-- unluac-runtime:         check((weak[1] ~= nil) == (key == "PLAIN_VALUE"), "operand root lifetime changed")
-- unluac-runtime:         events[#events + 1] = "write:" .. value
-- unluac-runtime:     end,
-- unluac-runtime: })
-- unluac-runtime: setfenv(run, env)
-- unluac-runtime: run()
-- unluac-runtime: check(table.concat(events, ",") == "read:COMPOUND_VALUE,add:1,write:11,read:COMPOUND_VALUE,sub:2,write:8,read:COMPOUND_VALUE,mul:3,write:30,read:COMPOUND_VALUE,div:4,write:2.5,read:COMPOUND_VALUE,mod:5,write:0,read:COMPOUND_VALUE,pow:2,write:100,read:PLAIN_VALUE,add:1,write:11")
-- unluac-runtime: report("compound-global-frame", table.concat(events, ","))
COMPOUND_VALUE = 10
PLAIN_VALUE = 10
COMPOUND_VALUE += 1
COMPOUND_VALUE -= 2
COMPOUND_VALUE *= 3
COMPOUND_VALUE /= 4
COMPOUND_VALUE %= 5
COMPOUND_VALUE ^= 2
PLAIN_VALUE = PLAIN_VALUE + 1
