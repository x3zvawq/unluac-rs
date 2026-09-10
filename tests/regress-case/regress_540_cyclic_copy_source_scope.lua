-- 源码 copy 只在循环体内可见；debug 修改后的当前值才允许跨作用域交接保活。
local gc = collectgarbage
local weak = setmetatable({}, { __mode = "v" })
local iteration = 0
local env = _G
local oldmeta = getmetatable(env)
local function make()
    local object = {}
    weak[1] = object
    return object
end
local function inspect()
    local found = false
    for index = 1, 40 do
        local name, value = debug.getlocal(2, index)
        if not name then break end
        if name == "copy" then
            found = true
            if value ~= weak[1] then error("copy source identity changed") end
            if iteration == 1 then debug.setlocal(2, index, nil) end
            break
        end
    end
    if not found then error("copy source binding missing") end
    gc("collect")
    if iteration == 1 and weak[1] ~= nil then error("hidden copy survived debug write") end
end
env.regress_540_missing_gc = nil
setmetatable(env, { __index = function(_, key)
    if key == "regress_540_missing_gc" then
        for index = 1, 40 do
            local name = debug.getlocal(2, index)
            if not name then break end
            if name == "copy" then error("copy visible outside source scope") end
        end
        gc("collect")
        if iteration == 1 and weak[1] == nil then error("copy died during header lookup") end
        return gc
    end
end })
while true do
    regress_540_missing_gc("collect")
    if weak[1] ~= nil then error("copy survived header overwrite") end
    if iteration == 2 then break end
    local owner = make()
    local copy = owner
    owner = inspect
    owner()
    if iteration == 0 and weak[1] == nil then error("copy died before backedge") end
    iteration = iteration + 1
end
setmetatable(env, oldmeta)
print("regress_540_cyclic_copy_source_scope", "OK")
