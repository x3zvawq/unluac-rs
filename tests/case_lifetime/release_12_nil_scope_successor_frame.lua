-- nil 声明的前缀和末端必须一起恢复；第二个原低槽 CALL 不能保活旧 do 内的读取结果。
local weak = setmetatable({}, {__mode = "v"})
local calls = 0
local old = getmetatable(_G)
local function make()
    calls = calls + 1
    if calls == 2 then
        collectgarbage("collect")
        assert(weak[1] == nil)
        print("scope-observed-value", weak[1] ~= nil)
    end
    return "9.125"
end
setmetatable(_G, {__index = function(_, key)
    if key == "for_skip_observe" then
        weak[1] = {}
        return weak[1]
    end
end})
local function followed()
    for index = make(), 1, 1 do error("entered") end
    do
        local cleared = nil
        local observed = for_skip_observe
    end
    for index = make(), 1, 1 do error("entered") end
end
followed()
calls = 0
local function followed_assignment()
    for index = make(), 1, 1 do error("entered") end
    do
        local cleared = nil
        local observed = for_skip_observe
    end
    nil_scope_sink = make()
end
followed_assignment()
assert(nil_scope_sink == "9.125")
nil_scope_sink = nil
calls = 0
local function followed_condition()
    for index = make(), 1, 1 do error("entered") end
    do
        local cleared = nil
        local observed = for_skip_observe
    end
    if make() then return 1 else return 2 end
end
assert(followed_condition() == 1)
calls = 0
local function followed_comparison()
    for index = make(), 1, 1 do error("entered") end
    do
        local cleared = nil
        local observed = for_skip_observe
    end
    if make() == "9.125" then return 1 else return 2 end
end
assert(followed_comparison() == 1)
calls = 0
local function followed_while()
    for index = make(), 1, 1 do error("entered") end
    do
        local cleared = nil
        local observed = for_skip_observe
    end
    while make() do
        if calls == 3 then break end
    end
end
followed_while()
assert(calls == 3)
setmetatable(_G, old)
