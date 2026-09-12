-- 单值短路位置的 vararg 是入口首值，参与成本与综合时应和普通 ref 一样计为一个原子。
local function choose(a,b,c,d,e,...)
    return a and (...) or b and (...) or c and (...) or d and (...) or e and (...)
end

for bits = 0, 31 do
    local a = bits % 2 == 1
    local b = math.floor(bits / 2) % 2 == 1
    local c = math.floor(bits / 4) % 2 == 1
    local d = math.floor(bits / 8) % 2 == 1
    local e = bits >= 16
    print("vararg", bits, choose(a,b,c,d,e), choose(a,b,c,d,e,false), choose(a,b,c,d,e,"tail","extra"))
end
