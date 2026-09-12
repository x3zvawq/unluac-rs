-- 纯 Decision 的共享尾在图内归约，不能先生成指数表达式再提取共同式。
-- unluac: expect-not-contains [[p1_1 and (not p1_3]]
-- unluac: expect-not-contains [[b and (not d]]
local function choose(a, b, c, d)
    return a and (b or c) and not d or (a or d) and b and c
end

local function expected(a, b, c, d)
    if a then
        local selected = b or c
        if selected and not d then return true end
    end
    local selected = a or d
    if not selected then return selected end
    if not b then return b end
    return c
end

local function wide(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p)
    return (a and (b or c) and not d or (a or d) and b and c)
        or (e and (f or g) and not h or (e or h) and f and g)
        or (i and (j or k) and not l or (i or l) and j and k)
        or (m and (n or o) and not p or (m or p) and n and o)
end

local unexpected = 0
local mt = {__eq = function()
    unexpected = unexpected + 1
    return false
end}
local object, other = setmetatable({}, mt), setmetatable({}, mt)
local values = {[1]=nil, [2]=false, [3]=true, [4]=0, [5]="", [6]=object, [7]=other}
for encoded = 0, 2400 do
    local a = values[encoded % 7 + 1]
    local b = values[math.floor(encoded / 7) % 7 + 1]
    local c = values[math.floor(encoded / 49) % 7 + 1]
    local d = values[math.floor(encoded / 343) % 7 + 1]
    assert(rawequal(choose(a,b,c,d), expected(a,b,c,d)))
end
assert(unexpected == 0)
assert(wide() == nil)
assert(wide(false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false) == false)
assert(rawequal(wide(false,false,false,false,false,false,false,false,false,false,false,false,true,true,other,true), other))
print("regress_564_pure_decision_graph", "OK")
