-- 跨回边的独立副本越过下轮全局查找，在原参数槽覆盖后退休。
-- unluac: expect-ast-min [[while]] [[1]]
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
env.regress_537_missing_gc = nil
setmetatable(env, { __index = function(_, key)
    if key == "regress_537_missing_gc" then
        gc("collect")
        if iteration > 0 then
            if weak[1] == nil then error("old copy died during next header lookup") end
        end
        return gc
    end
end })
while true do
    regress_537_missing_gc("collect")
    if weak[1] ~= nil then error("old copy survived header argument overwrite") end
    if iteration == 2 then break end
    local owner = make()
    local copy = owner
    owner = gc
    owner("collect")
    if weak[1] == nil then error("copy died before loop backedge") end
    iteration = iteration + 1
end
setmetatable(env, oldmeta)
print("regress_537_cyclic_copy_root", "OK")
