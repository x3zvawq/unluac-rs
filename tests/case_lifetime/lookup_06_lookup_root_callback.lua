-- lookup 的原覆盖端点独立于 callback 是否能被识别为 collectgarbage。
-- unluac: expect-ast-max [[local-binding]] [[8]]
-- 原交换快照和 copied 共用所需值，后续调用不再额外声明 callee 或 assert 中转。
-- unluac: expect-ast-max [[local-binding]] [[5]] [[@proto=0]]
-- unluac: expect-not-contains [[ = assert]]
-- unluac: expect-ast-count [[function]] [[2]]
local weak = setmetatable({}, {__mode = "k"})
local function run(gc)
    local tree = {}
    local child = {4, 9}
    tree.nodes = child
    local key = tree.nodes
    child = weak
    child[key] = true
    tree.nodes = nil
    child = gc
    key = "collect"
    child(key)
    child("collect")
    assert(next(weak) == nil)
    print("callback-key", next(weak) ~= nil)
end
run(collectgarbage)

-- 并行赋值读取旧 callable 快照，纯 copy 不丢失后续观察的身份。
local first, second = function() error("wrong callable") end, collectgarbage
first, second = second, first
local copied = first
run(copied)
