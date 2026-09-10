-- debug end 恢复寄存器复用，不能在下一条可观察 GGET 之前主动清槽。
local gc, next_key = collectgarbage, next
local env = _G
local weak = setmetatable({}, { __mode = "k" })
local observed
env.regress_525_missing_gc = nil
setmetatable(env, {
    __index = function(_, name)
        if name == "regress_525_missing_gc" then
            gc("collect")
            observed = next_key(weak) ~= nil
            assert(observed, "debug end cleared a root before global lookup")
            return gc
        end
    end,
})
do
    local scoped = {}
    weak[scoped] = true
    local function use(value) assert(value ~= nil) end
    use(scoped)
end
regress_525_missing_gc("collect")
assert(next_key(weak) == nil, "debug object outlived the following call")
setmetatable(env, nil)
print("regress_525_debug_scope_lookup_root", observed, "closed")
