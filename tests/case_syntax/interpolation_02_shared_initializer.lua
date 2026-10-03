-- 共享的插值结果只保留源码声明；高槽调用准备与低槽 COPY 整体退休。
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=1]]
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=2]]
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=3]]
-- unluac: expect-ast-count [[method-call]] [[1]] [[@proto=5]]
local function decorate(tag, value)
    local body = `{tag}:{value}`
    return `[{body}] len={#body}`
end
local function observed(tag, value, observe)
    local body = `{observe(tag)}:{observe(value)}`
    return `[{body}] len={#body}`
end
local function captured(tag, value)
    local body = `{tag}:{value}`
    return function() return body, #body end
end
local function explicit()
    local result
    result = ("literal%%"):format()
    return result
end
assert(decorate("k", 3) == "[k:3] len=3")
assert(decorate("long", 42) == "[long:42] len=7")
local trace = {}
local function observe(value)
    trace[#trace + 1] = tostring(value)
    return value, "extra"
end
assert(observed("v", 4, observe) == "[v:4] len=3")
assert(#trace == 2 and table.concat(trace, "|") == "v|4")
local read = captured("hold", 5)
assert(read() == "hold:5")
local body, length = read()
assert(body == "hold:5" and length == 6)
assert(explicit() == "literal%")
print(decorate("k", 3), observed("x", 8, observe), body, length, explicit())
assert(#trace == 4 and table.concat(trace, "|") == "v|4|x|8")
