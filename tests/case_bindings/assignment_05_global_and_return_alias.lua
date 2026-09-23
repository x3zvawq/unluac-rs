-- unluac: expect-not-contains [[xmin, ymin, xmax, ymax =]]
-- unluac: expect-not-contains [[local r1_0 = p1_0]]
-- x/y/radius 的写入保持原参数身份；多结果 CALL 仍一次初始化四个低槽副本。
-- unluac: expect-contains [[local r1_0, r1_1, r1_2, r1_3 = p1_0:getAdjustedRect()]]
-- unluac: expect-contains [[ymax = r1_3]]
-- unluac: expect-contains [[xmin = r1_0]]
-- unluac: expect-contains [[return p1_1, p1_2, p1_3]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
-- CALL 初始化以当前事务的左值归属为准，不因后续 owner 合并退回空声明。
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=0]]
-- 多返回值完成全局写入后，参数算术仍按原准备槽求值，不保留逐指令中转。
-- unluac: expect-contains [[p1_1 = (xmin + xmax) / 2]]
-- unluac: expect-contains [[p1_2 = (ymin + ymax) / 2]]
-- unluac: expect-contains [[p1_3 = math.min((xmax - xmin) / 2, (ymax - ymin) / 2)]]
-- unluac: expect-contains [[local r2_4 = math.abs(r2_2 - r2_0)]]
-- 保留原 height 初始化与 CALL 槽；不强制把它改成返回参数区里的新调用。
-- unluac: expect-contains [[local r2_5 = math.abs(r2_3 - r2_1)]]
-- unluac: expect-contains [[return r2_4, r2_5]]
-- 完整数组直接写回原捕获 cell，不能让临时声明占住后续 CALL 的准备区。
-- unluac: expect-contains [[r0_3 = { 10, 16, 2, 4 }]]
-- unluac: expect-count [[r0_3 = { 2, 4, 10, 16 }]] [[2]]
-- 循环内写回同一低槽，不能改成新声明后再逐项交接。
-- unluac: expect-count [[r0_8, r0_9 = r0_1(r0_4)]] [[3]]
-- 条件末项的算术按原短路顺序在 Boolean 槽求值，不拆出 callee 和参数别名。
-- unluac: expect-contains [[assert(r0_8 == 0 and r0_9 == 0 and r0_2 == 3 + r0_10)]]
-- unluac: expect-not-contains [[unluac error]]

local function circle(self, x, y, radius)
    if not (x and y and radius) then
        xmin, ymin, xmax, ymax = self:getAdjustedRect()
        x = (xmin + xmax) / 2
        y = (ymin + ymax) / 2
        radius = math.min((xmax - xmin) / 2, (ymax - ymin) / 2)
    end
    return x, y, radius
end

local function size(self)
    local xmin, ymin, xmax, ymax = self:getAdjustedRect()
    if xmin == nil or ymin == nil or xmax == 0 or ymax == 0 then
        return 0, 0
    end
    local width = math.abs(xmax - xmin)
    local height = math.abs(ymax - ymin)
    return width, height
end

local calls = 0
local bounds = { 2, 4, 10, 16 }
local owner = {}
function owner:getAdjustedRect()
    assert(self == owner)
    calls = calls + 1
    return unpack(bounds, 1, 4)
end
local x, y, r = circle(owner, 0, 0, 0)
assert(x == 0 and y == 0 and r == 0 and calls == 0)
x, y, r = circle(owner, nil, 1, 2)
assert(x == 6 and y == 10 and r == 4 and calls == 1)
assert(xmin == 2 and ymin == 4 and xmax == 10 and ymax == 16)
local w, h = size(owner)
assert(w == 8 and h == 12 and calls == 2)
bounds = { 10, 16, 2, 4 }
w, h = size(owner)
assert(w == 8 and h == 12 and calls == 3)
for invalid = 1, 4 do
    bounds = { 2, 4, 10, 16 }
    if invalid <= 2 then bounds[invalid] = nil else bounds[invalid] = 0 end
    w, h = size(owner)
    assert(w == 0 and h == 0 and calls == 3 + invalid)
end
print("regress_64#1", x, y, r, xmin, ymin, xmax, ymax, calls)
