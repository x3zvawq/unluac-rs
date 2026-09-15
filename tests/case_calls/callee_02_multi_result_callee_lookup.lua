-- callee lookup 内仍可观察第二个旧根，只有进入实际调用后它才退出 caller 根域。
local gc = collectgarbage
local weak = setmetatable({}, { __mode = "v" })
local left, right
local function make_pair() return {}, {} end
local function replace_pair()
    left, right = nil, nil
    gc("collect")
    assert(weak[1] == nil and weak[2] == nil, "old roots survived replacement call")
    return _G, 1
end
local dispatch = setmetatable({}, { __index = function(_, key)
    assert(key == "missing")
    left, right = nil, nil
    gc("collect")
    assert(weak[2] ~= nil, "second old root died during callee lookup")
    return replace_pair
end })
left, right = make_pair()
weak[1], weak[2] = left, right
local env, tag = dispatch.missing()
gc("collect")
assert(weak[1] == nil and weak[2] == nil, "old roots survived parallel debug write")
assert(env == _G and tag == 1)
print("regress_536_multi_result_callee_lookup", "OK")
