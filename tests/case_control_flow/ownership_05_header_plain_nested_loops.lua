-- regress_128_same_header_plain_nested_loops#1: 普通 while/repeat 共用 header 时仍是两个严格嵌套 loop
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[::L]]
local subject = function(a, b)
    repeat
        while a do
            if b then
                break
            end
        end
    until b
end

local dispatch = { subject }
assert(select("#", dispatch[1](false, true)) == 0)
assert(select("#", dispatch[1](true, true)) == 0)
assert(select("#", dispatch[1](nil, 0)) == 0)
assert(select("#", dispatch[1](0, "")) == 0)
assert(select("#", dispatch[1]("", 0)) == 0)
-- 空 while 正文的 break 检查也可作为第二项循环条件，仍保留两层循环。
print("regress_128#1", "empty-while", "inner-break")
