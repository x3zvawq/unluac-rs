-- 多返回值的两个匿名 home 分别在 callee 准备与调用入口退休，捕获 cell 清空可观察其差异。
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
left, right = make_pair()
weak[1], weak[2] = left, right
local env, tag = replace_pair()
gc("collect")
assert(weak[1] == nil and weak[2] == nil, "old roots survived parallel debug write")
assert(env == _G and tag == 1)
print("regress_535_multi_result_frame_roots", "OK")
