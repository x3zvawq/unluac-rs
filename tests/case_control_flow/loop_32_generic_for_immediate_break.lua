-- regress_32_generic_for_immediate_break#1: generic-for with immediate body break should stay structured
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local touches = {
    first = {
        x = 1,
    },
    second = {
        x = 2,
    },
}

local touch_id = nil

local function pick_first_touch()
    if touch_id == nil then
        for id, _touch in pairs(touches) do
            touch_id = id
            break
        end
    end

    return touch_id ~= nil
end

local picked = pick_first_touch()
assert(picked == true and touch_id ~= nil)
print("regress_32_generic_for_immediate_break#1", picked)
-- 已选择时完全跳过 iterator setup；不依赖 pairs 的首键顺序。
local selected = touch_id
setfenv(pick_first_touch, setmetatable({pairs = function()
    error("iterator must not run after selection")
end}, {__index = getfenv()}))
assert(pick_first_touch() == true and touch_id == selected)
setfenv(pick_first_touch, getfenv())
touch_id, touches = nil, {}
assert(pick_first_touch() == false and touch_id == nil)
touches = {only = {x = 3}}
assert(pick_first_touch() == true and touch_id == "only")
-- 非 nil 的 false 也已经选定，不能把显式 ~= nil 改成普通真值判断。
touch_id = false
assert(pick_first_touch() == true and touch_id == false)
-- unluac: expect-ast-count [[local-binding]] [[5]] [[@proto=0]]
-- LuaJIT 的子函数编号与 PUC 相反；两个方言均固定各自的循环体和失败回调。
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=2]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=2]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=2]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=2]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=luajit]]
-- 两项逆序发布应收回 nil 准备，后续构造器和调用不再经过额外别名。
-- unluac: expect-ast-count [[assign]] [[3]] [[@proto=0]]
-- unluac: expect-ast-count [[call]] [[16]] [[@proto=0]]
-- unluac: expect-ast-count [[table-constructor]] [[8]] [[@proto=0]]
-- 仅在未选择时初始化 iterator，一次写回后立即 break；返回保留显式非 nil 检查。
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=2]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=2]]
