-- 长纯逻辑链复用逐节点求值事实；无 debug 输入也必须保持短路结果。
-- unluac: expect-not-contains [[unluac error]]
local function check(p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30,p31,p32,p33,p34,p35,p36,p37,p38,p39,p40,p41,p42,p43,p44,p45,p46,p47,p48,p49,p50,p51,p52,p53,p54,p55,p56,p57,p58,p59,p60,p61,p62,p63)
 return p0 == nil and p1 == nil and p2 == nil and p3 == nil and p4 == nil and p5 == nil and p6 == nil and p7 == nil and p8 == nil and p9 == nil and p10 == nil and p11 == nil and p12 == nil and p13 == nil and p14 == nil and p15 == nil and p16 == nil and p17 == nil and p18 == nil and p19 == nil and p20 == nil and p21 == nil and p22 == nil and p23 == nil and p24 == nil and p25 == nil and p26 == nil and p27 == nil and p28 == nil and p29 == nil and p30 == nil and p31 == nil and p32 == nil and p33 == nil and p34 == nil and p35 == nil and p36 == nil and p37 == nil and p38 == nil and p39 == nil and p40 == nil and p41 == nil and p42 == nil and p43 == nil and p44 == nil and p45 == nil and p46 == nil and p47 == nil and p48 == nil and p49 == nil and p50 == nil and p51 == nil and p52 == nil and p53 == nil and p54 == nil and p55 == nil and p56 == nil and p57 == nil and p58 == nil and p59 == nil and p60 == nil and p61 == nil and p62 == nil and p63 == nil
end
assert(check() == true)
assert(check(1) == false)
assert(check(nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,nil,false) == false)
print("regress493", check(), check(1))
