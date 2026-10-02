-- 并列上值写回等待全部 RHS 完成，失败的后项不能提前发布前项结果。
-- 三个子函数的逆序编号仍使 assign_pair 在所有方言中对应 proto#2。
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]]
-- 三项常量重置应整体恢复，不为首项留下独立的高槽中转变量。
-- unluac: expect-ast-max [[local-binding]] [[12]] [[@proto=0]]
-- unluac: expect-contains [[first, second = value("L"), value("R")]] [[@debug=retained]]
local first, second = 0, 0
local trace, fail = "", true
local spare, count, tail = "old", -1, -1
local function value(tag)
    assert(first == 0 and second == 0)
    trace = trace .. tag
    if fail and tag == "R" then error("right failed", 0) end
    return { tag = tag }
end
local function assign_pair()
    first, second = value("L"), value("R")
    -- JIT 先准备表与 count，末项常量直接写 tail，再逆序发布前两项。
    spare, count, tail = {}, 0, 0
end
local function overlap()
    first, first = value("L"), value("R")
end

local ok, message = pcall(assign_pair)
assert(not ok and message == "right failed")
assert(first == 0 and second == 0 and trace == "LR")
assert(spare == "old" and count == -1 and tail == -1)
fail, trace = false, ""
assign_pair()
assert(first.tag == "L" and second.tag == "R" and trace == "LR")
assert(first ~= second)
assert(type(spare) == "table" and next(spare) == nil and count == 0 and tail == 0)
print("parallel upvalue values", first.tag, second.tag, trace)
first, second, trace = 0, 0, ""
overlap()
assert(second == 0 and trace == "LR")
-- 重复目标的最终值由该方言原写回顺序决定，运行对照须保留这一可观察差异。
print("overlapping upvalue writes", first.tag, trace)
