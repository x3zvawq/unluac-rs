-- 原声明帧在 numeric-for header 前结束；不提前清根，保留header求值和额外别名的观察。
-- integer_skip
do
local weak = setmetatable({}, {__mode="v"})
local observations = {}
local old = getmetatable(_G)
local function observe()
    collectgarbage("collect")
    observations[#observations+1] = tostring(weak[1] ~= nil)
end
local function header(argument)
    observe()
    return 9
end
setmetatable(_G, {__index=function(_, key)
    if key == "for_binding_after" then observe(); return 0 end
    if key == "for_binding_start" then observe(); return 9 end
    if key == "for_binding_argument" then observe(); return 1 end
end})
local function probe()
    
    do
        local a,b,c,object = false,false,false,{}
        weak[1] = object
        
    end
    for index = 9, 1, 1 do error("entered") end
    local observed = for_binding_after
    return observed
end
probe()
setmetatable(_G, old)
local result = table.concat(observations, ",")
print("integer_skip", result)
assert(result == "false")

end
-- float_once
do
local weak = setmetatable({}, {__mode="v"})
local observations = {}
local old = getmetatable(_G)
local function observe()
    collectgarbage("collect")
    observations[#observations+1] = tostring(weak[1] ~= nil)
end
local function header(argument)
    observe()
    return 9
end
setmetatable(_G, {__index=function(_, key)
    if key == "for_binding_after" then observe(); return 0 end
    if key == "for_binding_start" then observe(); return 9 end
    if key == "for_binding_argument" then observe(); return 1 end
end})
local function probe()
    
    do
        local a,b,c,object = false,false,false,{}
        weak[1] = object
        
    end
    for index = 9.125, 9.125, 1 do  end
    local observed = for_binding_after
    return observed
end
probe()
setmetatable(_G, old)
local result = table.concat(observations, ",")
print("float_once", result)
assert(result == "false")

end
-- low_prefix
do
local weak = setmetatable({}, {__mode="v"})
local observations = {}
local old = getmetatable(_G)
local function observe()
    collectgarbage("collect")
    observations[#observations+1] = tostring(weak[1] ~= nil)
end
local function header(argument)
    observe()
    return 9
end
setmetatable(_G, {__index=function(_, key)
    if key == "for_binding_after" then observe(); return 0 end
    if key == "for_binding_start" then observe(); return 9 end
    if key == "for_binding_argument" then observe(); return 1 end
end})
local function probe()
    local prefix = "kept"
    do
        local a,b,c,object = false,false,false,{}
        weak[1] = object
        
    end
    for index = 9, 1, 1 do error("entered") end
    local observed = for_binding_after
    return prefix, observed
end
probe()
setmetatable(_G, old)
local result = table.concat(observations, ",")
print("low_prefix", result)
assert(result == "false")

end
-- alias_survives
do
local weak = setmetatable({}, {__mode="v"})
local observations = {}
local old = getmetatable(_G)
local function observe()
    collectgarbage("collect")
    observations[#observations+1] = tostring(weak[1] ~= nil)
end
local function header(argument)
    observe()
    return 9
end
setmetatable(_G, {__index=function(_, key)
    if key == "for_binding_after" then observe(); return 0 end
    if key == "for_binding_start" then observe(); return 9 end
    if key == "for_binding_argument" then observe(); return 1 end
end})
local function probe()
    
    do
        local a,b,c,object = false,false,false,{}
        weak[1] = object
        local alias = object
        weak[1] = alias
    end
    for index = 9, 1, 1 do error("entered") end
    local observed = for_binding_after
    return observed
end
probe()
setmetatable(_G, old)
local result = table.concat(observations, ",")
print("alias_survives", result)
assert(result == "true")

end
-- alias_cleared
do
local weak = setmetatable({}, {__mode="v"})
local observations = {}
local old = getmetatable(_G)
local function observe()
    collectgarbage("collect")
    observations[#observations+1] = tostring(weak[1] ~= nil)
end
local function header(argument)
    observe()
    return 9
end
setmetatable(_G, {__index=function(_, key)
    if key == "for_binding_after" then observe(); return 0 end
    if key == "for_binding_start" then observe(); return 9 end
    if key == "for_binding_argument" then observe(); return 1 end
end})
local function probe()
    
    do
        local a,b,c,object = false,false,false,{}
        weak[1] = object
        local alias = object
        weak[1] = alias
        alias = nil
    end
    for index = 9, 1, 1 do error("entered") end
    local observed = for_binding_after
    return observed
end
probe()
setmetatable(_G, old)
local result = table.concat(observations, ",")
print("alias_cleared", result)
assert(result == "false")

end
-- global_header
do
local weak = setmetatable({}, {__mode="v"})
local observations = {}
local old = getmetatable(_G)
local function observe()
    collectgarbage("collect")
    observations[#observations+1] = tostring(weak[1] ~= nil)
end
local function header(argument)
    observe()
    return 9
end
setmetatable(_G, {__index=function(_, key)
    if key == "for_binding_after" then observe(); return 0 end
    if key == "for_binding_start" then observe(); return 9 end
    if key == "for_binding_argument" then observe(); return 1 end
end})
local function probe()
    
    do
        local a,b,c,object = false,false,false,{}
        weak[1] = object
        
    end
    for index = for_binding_start, 1, 1 do error("entered") end
    local observed = for_binding_after
    return observed
end
probe()
setmetatable(_G, old)
local result = table.concat(observations, ",")
print("global_header", result)
assert(result == "true,false")

end
-- call_header
do
local weak = setmetatable({}, {__mode="v"})
local observations = {}
local old = getmetatable(_G)
local function observe()
    collectgarbage("collect")
    observations[#observations+1] = tostring(weak[1] ~= nil)
end
local function header(argument)
    observe()
    return 9
end
setmetatable(_G, {__index=function(_, key)
    if key == "for_binding_after" then observe(); return 0 end
    if key == "for_binding_start" then observe(); return 9 end
    if key == "for_binding_argument" then observe(); return 1 end
end})
local function probe()
    
    do
        local a,b,c,object = false,false,false,{}
        weak[1] = object
        
    end
    for index = header(1), 1, 1 do error("entered") end
    local observed = for_binding_after
    return observed
end
probe()
setmetatable(_G, old)
local result = table.concat(observations, ",")
print("call_header", result)
assert(result == "false,false")

end
-- argument_header
do
local weak = setmetatable({}, {__mode="v"})
local observations = {}
local old = getmetatable(_G)
local function observe()
    collectgarbage("collect")
    observations[#observations+1] = tostring(weak[1] ~= nil)
end
local function header(argument)
    observe()
    return 9
end
setmetatable(_G, {__index=function(_, key)
    if key == "for_binding_after" then observe(); return 0 end
    if key == "for_binding_start" then observe(); return 9 end
    if key == "for_binding_argument" then observe(); return 1 end
end})
local function probe()
    
    do
        local a,b,c,object = false,false,false,{}
        weak[1] = object
        
    end
    for index = header(for_binding_argument), 1, 1 do error("entered") end
    local observed = for_binding_after
    return observed
end
probe()
setmetatable(_G, old)
local result = table.concat(observations, ",")
print("argument_header", result)
assert(result == "true,false,false")

end
-- 参数快照root owner的已有身份不能被新声明帧覆盖。
do
local weak = setmetatable({}, {__mode = "v"})
local results = {}
local old = getmetatable(_G)
local function header(a, b, c)
    collectgarbage("collect")
    results[2] = tostring(weak[1] ~= nil)
    return 9
end
setmetatable(_G, {__index = function(_, key)
    if key == "for_binding_argument" then
        debug.setlocal(2, 1, nil)
        collectgarbage("collect")
        results[1] = tostring(weak[1] ~= nil)
        return 3
    elseif key == "for_binding_after" then
        collectgarbage("collect")
        results[3] = tostring(weak[1] ~= nil)
        return 0
    end
end})
local function probe(object)
    do
        local a, b, c, copy = false, false, false, object
        weak[1] = copy
    end
    for index = header(1, 2, for_binding_argument), 1 do error("entered") end
    return for_binding_after
end
probe({})
setmetatable(_G, old)
local result = table.concat(results, ",")
print("parameter-holder", result)
assert(result == "true,false,false")

end
