-- regress_205_while_true_header_guard#1: while-true 的正文 header guard 不能误认成 repeat 尾条件
-- unluac: expect-contains [[while true do]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- 两轮分别经过正常尾部和 header guard break，仍是一个 while-true。
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=0]]
-- unluac: expect-ast-count [[repeat]] [[0]] [[@proto=0]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=0]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=0]]
local i = 0
while true do
    print("regress_205_while_true_header_guard#1", 1)
    i = i + 1
    if i ~= 1 then
        break
    end
    print("regress_205_while_true_header_guard#1", 2)
end
assert(i == 2)
