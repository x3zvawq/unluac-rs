-- 两次 CALL 之间先经过不写结果 home 的 TEST；覆盖证书必须包括后续所有路径。
-- 观察输出使用每个 VM 自己的源码基线，不假设不同 VM 具有相同的弱根时机。
-- unluac: expect-not-contains [[if p1_0 then]]
-- unluac: expect-not-contains [[if a then]]
local function direct(a,b,first,second,fallback)
    return a and not first() or b and not second() or fallback()
end

local function lookup(left,right,first,methods)
    return left and not first() or right and not methods.second() or methods.fallback()
end

local weak = setmetatable({}, {__mode="v"})
local trace = {}
local function observe(label)
    collectgarbage("collect")
    collectgarbage("collect")
    trace[#trace+1] = label .. ":" .. tostring(weak.value ~= nil)
end
local function first()
    trace[#trace+1] = "first"
    local value = {}
    weak.value = value
    return value
end
local function second()
    observe("second")
    return true
end
local function fallback()
    observe("fallback")
    return "done"
end
local methods = setmetatable({}, {__index=function(_, key)
    observe("lookup-" .. key)
    if key == "second" then return second end
    return fallback
end})

print("direct-both", direct(true,true,first,second,fallback))
print("direct-skip-second", direct(true,false,first,second,fallback))
print("direct-skip-first", direct(false,true,first,second,fallback))
print("lookup-both", lookup(true,true,first,methods))
print("lookup-skip-second", lookup(true,false,first,methods))

local function falsy() return false end
local function absent() return nil end
print("false-first", direct(true,true,falsy,second,fallback))
print("nil-first", direct(true,true,absent,second,fallback))
print("false-second", direct(true,true,first,falsy,fallback))
print("nil-second", direct(true,true,first,absent,fallback))
print("trace", table.concat(trace, ","))
