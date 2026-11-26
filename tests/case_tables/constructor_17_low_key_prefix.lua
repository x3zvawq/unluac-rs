-- 原键位于表分配槽以下，后继回调按原声明位置替换第二个 local。
-- 删除键声明会把表移到第一槽，导致写回失败或改写错误对象。
local function replace()
    assert(debug.setlocal(2, 2, {x = 9}) ~= nil)
end
local function run()
    local key = "x"
    local values = {[key] = 1}
    replace()
    return values.x
end
assert(run() == 9)
print("constant-key-prefix")
