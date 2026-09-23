-- 原高槽 CALL 的单结果经两次低槽 MOVE 写回；完整帧须保留赋值和后继 COPY，避免每轮新增 callee。
-- 返回 COPY 只承担原返回槽，不能继承同名 HIR local 的旧 CALL 写域而产生中转声明。
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[2]] [[@proto=1]]
-- unluac: expect-contains [[return first, second, target]] [[@debug=retained]]
-- unluac: expect-contains [[if _VERSION == "Lua 5.1" then]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]] [[@dialect=lua5.5]]
local function probe(argument)
    local first, second = "left", "right"
    local target = type
    local alias = target
    alias = alias(argument)
    target = alias
    return first, second, target
end
local a,b,c = probe({})
assert(a=="left" and b=="right" and c=="table")
print(a,b,c)

-- SETTABUP 在 CALL 后读取当前上值 cell；Lua5.1 的 GETUPVAL 则先保存目标表。
local target = {}
local original_target = target
local replacement = {}
local function fill(callback)
    target.value = callback()
end
local function replace_target()
    target = replacement
    return 41
end
fill(replace_target)
if _VERSION == "Lua 5.1" then
    assert(original_target.value == 41 and replacement.value == nil)
else
    assert(original_target.value == nil and replacement.value == 41)
end
