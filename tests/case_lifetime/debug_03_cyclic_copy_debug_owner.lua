-- assert 值物化形成 label flow；debug source owner 与跨轮副本必须分别退休。
-- owner 的原 COPY 覆盖沿用同一身份，跨轮 copy 独立保活；assert 的函数和布尔实参不落地。
-- unluac: expect-ast-max [[local-binding]] [[8]] [[@proto=0]]
-- unluac: expect-not-contains [[ = assert]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[break]] [[1]]
-- unluac: expect-contains [[local owner = make()]] [[@debug=retained]]
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
env.regress_538_missing_gc = nil
setmetatable(env, { __index = function(_, key)
    if key == "regress_538_missing_gc" then
        gc("collect")
        if iteration > 0 then
            assert(weak[1] ~= nil, "old copy died during next header lookup")
        end
        return gc
    end
end })
while true do
    regress_538_missing_gc("collect")
    assert(weak[1] == nil, "old copy survived header argument overwrite")
    if iteration == 2 then break end
    local owner = make()
    local copy = owner
    owner = gc
    owner("collect")
    assert(weak[1] ~= nil, "copy died before loop backedge")
    iteration = iteration + 1
end
setmetatable(env, oldmeta)
print("regress_538_cyclic_copy_debug_owner", "OK")
