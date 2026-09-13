-- 比较 CALL 的表结果须跨元方法和 callee 查找存活，到原参数/后继写才释放。
local weak = setmetatable({}, {__mode = "v"})
local observations = {}
local equal = false
local function observe(label)
    collectgarbage("collect")
    observations[#observations + 1] = label .. ":" .. tostring(weak[1] ~= nil)
end
local meta = {__eq = function()
    observe("eq")
    return equal
end}
local left = setmetatable({}, meta)
local function make()
    local value = setmetatable({}, meta)
    weak[1] = value
    return value
end
local function initial()
    return "9.125"
end
local function next_call()
    observe("next-call")
    return "9.125"
end
local function then_callback(message)
    observe("then-call")
    assert(message == "replacement")
end
local old_meta = getmetatable(_G)
local old_error = error
error = nil
setmetatable(_G, {__index = function(_, key)
    if key == "comparison_seed" then
        return {}
    elseif key == "error" then
        observe("then-lookup")
        return then_callback
    elseif key == "comparison_after" then
        observe("after")
        return 0
    elseif key == "comparison_next" then
        observe("next-lookup")
        return next_call
    end
end})
local function then_case()
    for index = initial(), 1 do error("entered") end
    do
        local cleared = nil
        local value = comparison_seed
    end
    if left ~= make() then error("replacement") end
    return comparison_after
end
local function normal_case()
    for index = initial(), 1 do error("entered") end
    do
        local cleared = nil
        local value = comparison_seed
    end
    if left ~= make() then error("unexpected") end
    local prefix = 23
    for index = comparison_next(), 1 do error("entered") end
    return prefix, 42, comparison_after
end
then_case()
equal = true
local prefix, replacement = normal_case()
setmetatable(_G, old_meta)
error = old_error
assert(prefix == 23 and replacement == 42)
local result = table.concat(observations, ",")
print(result)
assert(result == "eq:true,then-lookup:true,then-call:false,after:false,eq:true,next-lookup:true,next-call:false,after:false")
