-- 非相邻 Boolean 分支仍可提取共同首项/末项；索引不能删掉原搜索的有效候选。
-- LuaJIT 的未知参数比较不属于这项纯表达式证明，因此形状合同仅用于 PUC Lua/Luau。
-- unluac: expect-contains [[p1_0 == 1 and (p1_1 == 2 or p1_3 == 4)]]
-- unluac: expect-contains [[(p2_0 == 1 or p2_3 == 4) and p2_1 == 2]]
local function prefix(a,b,c,d)
    return (a == 1 and b == 2) or c == 3 or (a == 1 and d == 4)
end
local function suffix(a,b,c,d)
    return (a == 1 and b == 2) or c == 3 or (d == 4 and b == 2)
end
local function nested(a,b,c,d,e)
    return ((a == 1 or b == 2) and c == 3) or e == 5
        or ((a == 1 or b == 2) and d == 4)
end
for bits = 0,31 do
    local a = bits % 2
    local b = math.floor(bits/2) % 2 * 2
    local c = math.floor(bits/4) % 2 * 3
    local d = math.floor(bits/8) % 2 * 4
    local e = math.floor(bits/16) % 2 * 5
    print("boolean", bits, prefix(a,b,c,d), suffix(a,b,c,d), nested(a,b,c,d,e))
end

-- 同一个候选索引命中不表示值级 or 可以交换顺序；nil/false 与不同 truthy 返回身份保留。
local function values(a,b,c,d)
    return a and b or c or a and d
end
local pool = {[2]=false, [3]=0, [4]="text"}
for bits = 0,255 do
    local a = pool[bits % 4 + 1]
    local b = pool[math.floor(bits/4) % 4 + 1]
    local c = pool[math.floor(bits/16) % 4 + 1]
    local d = pool[math.floor(bits/64) % 4 + 1]
    print("value", bits, values(a,b,c,d))
end
