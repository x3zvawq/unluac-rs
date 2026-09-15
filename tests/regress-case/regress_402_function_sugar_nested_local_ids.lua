-- regress_402_function_sugar_nested_local_ids: child LocalIds do not count as outer chain uses
-- unluac: expect-contains [[:begin():finish(function()]]

local function build(obj)
    local value = obj:begin()
    value:finish(function()
        local value = side()
        use(value)
        return value
    end)
end

-- begin 的 receiver 与 finish 的 receiver 不同，回调在 build 返回之后才执行。
local obj, chain, token = {}, {}, {}
local callbacks, log = {}, {}
function obj:begin()
    assert(self == obj)
    log[#log + 1] = "begin"
    return chain
end
function chain:finish(callback)
    assert(self == chain)
    log[#log + 1] = "finish"
    callbacks[#callbacks + 1] = callback
end
function side()
    log[#log + 1] = "side"
    return token
end
function use(value)
    assert(value == token)
    log[#log + 1] = "use"
end
assert(select("#", build(obj)) == 0)
assert(#callbacks == 1 and table.concat(log, ",") == "begin,finish")
assert(callbacks[1]() == token)
assert(table.concat(log, ",") == "begin,finish,side,use")
print("regress_402_nested_ids#1", table.concat(log, ","))
