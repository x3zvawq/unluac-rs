-- 新 debug 声明保持独立身份；旧调用结果根跨过 lookup 求值，写入完成后必须退休。
local gc = collectgarbage
local weak = setmetatable({}, { __mode = "v" })
local object
_G.regress_534_missing_env = nil
setmetatable(_G, { __index = function(_, key)
    if key == "regress_534_missing_env" then
        object = nil
        gc("collect")
        assert(weak[1] ~= nil, "old root died during overwrite lookup")
        return _G
    end
end })
object = setmetatable({}, {})
weak[1] = object
local env = regress_534_missing_env
gc("collect")
assert(weak[1] == nil, "old root survived debug overwrite")
assert(env == _G, "new debug identity changed")
setmetatable(_G, nil)
print("regress_534_debug_overwrite_lookup_root", "OK")
