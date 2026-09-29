-- 单值短路位置的 vararg 是入口首值，参与成本与综合时应和普通 ref 一样计为一个原子。
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-max [[local-binding]] [[9]]
local function choose(a,b,c,d,e,...)
    return a and (...) or b and (...) or c and (...) or d and (...) or e and (...)
end

local object = {}
local combinations = 0
for bits = 0, 31 do
    local a = bits % 2 == 1
    local b = math.floor(bits / 2) % 2 == 1
    local c = math.floor(bits / 4) % 2 == 1
    local d = math.floor(bits / 8) % 2 == 1
    local e = bits >= 16
    print("vararg", bits, choose(a,b,c,d,e), choose(a,b,c,d,e,false), choose(a,b,c,d,e,"tail","extra"))
    if e then
        assert(choose(a,b,c,d,e) == nil)
    else
        assert(choose(a,b,c,d,e) == false)
    end
    assert(choose(a,b,c,d,e,false,"extra") == false)
    if bits > 0 then
        assert(choose(a,b,c,d,e,"tail","extra") == "tail")
        assert(choose(a,b,c,d,e,0,"extra") == 0)
        assert(choose(a,b,c,d,e,"","extra") == "")
        assert(choose(a,b,c,d,e,object,"extra") == object)
    else
        assert(choose(a,b,c,d,e,object,"extra") == false)
    end
    assert(select("#", choose(a,b,c,d,e)) == 1)
    assert(select("#", choose(a,b,c,d,e,object,"extra")) == 1)
    combinations = combinations + 1
end
assert(combinations == 32)
assert(choose(nil,nil,nil,nil,nil,"tail") == nil)
assert(choose("",false,false,false,false,object) == object)
assert(choose(false,false,false,false,0,nil,"extra") == nil)
