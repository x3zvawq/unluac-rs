-- regress_128_same_header_plain_nested_loops#1: 普通 while/repeat 共用 header 时仍是两个严格嵌套 loop
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
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
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- 空 while 正文的 break 检查也可作为第二项循环条件，仍保留两层循环。
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[break]] [[0]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[break]] [[0]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[break]] [[0]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[break]] [[0]] [[@proto=1]] [[@dialect=luau]]
print("regress_128#1", "empty-while", "inner-break")
