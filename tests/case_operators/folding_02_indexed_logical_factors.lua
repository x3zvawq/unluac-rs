-- 非相邻 Boolean 分支不能因值相等而提取原比较的公因子，须保留出现次数与短路顺序。
-- unluac: expect-ast-count [[function]] [[4]]
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-ast-count [[numeric-for]] [[2]]
-- unluac: expect-ast-max [[local-binding]] [[18]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=3]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=4]]
-- floor 调用应与原算术 initializer 合并，不留下保存 callee 的中间声明。
-- unluac: expect-count [[math.floor(]] [[7]]
-- unluac: expect-contains [[return p1_0 == 1 and p1_1 == 2 or p1_2 == 3 or p1_0 == 1 and p1_3 == 4]]
-- unluac: expect-contains [[return p2_0 == 1 and p2_1 == 2 or p2_2 == 3 or p2_3 == 4 and p2_1 == 2]]
-- unluac: expect-count [[p3_0 == 1 or p3_1 == 2]] [[2]]
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

-- 返回的是原操作数，不能将 truthy 对象、0 和空串改成 Boolean；nil 与 false 也不能混同。
local first, last = {}, {}
assert(values(true, first, last, false) == first)
assert(values(true, false, last, first) == last)
assert(values(true, nil, false, last) == last)
assert(values(true, 0, last, false) == 0)
assert(values(true, "", last, false) == "")
assert(values(nil, first, false, last) == nil)
assert(values(false, first, nil, last) == false)
assert(select("#", values(nil, first, false, last)) == 1)
assert(select("#", prefix(1, 2, 0, 0)) == 1)
assert(select("#", suffix(0, 2, 0, 4)) == 1)
assert(select("#", nested(1, 0, 0, 4, 0)) == 1)
