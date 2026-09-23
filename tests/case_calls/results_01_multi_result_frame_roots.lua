-- 多返回值的两个匿名 home 分别在 callee 准备与调用入口退休，捕获 cell 清空可观察其差异。
-- LOADNIL 与逆序 SETUPVAL 恢复同一并行赋值，仍在观察调用之前清空两个 cell。
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
-- unluac: expect-contains [[left, right = nil, nil]] [[@debug=retained]]
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
