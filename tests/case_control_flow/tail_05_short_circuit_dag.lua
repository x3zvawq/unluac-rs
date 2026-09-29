-- regress_222_shared_short_circuit_dag#1: 多前驱的共享条件节点仍属于短路 DAG
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- 参数声明、两次原 TEST 和返回值各出现一次；稳定绑定也不能吸收第二次检查。
-- unluac: expect-count [[p1_0]] [[4]]
-- unluac: expect-ast-count [[repeat]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[7]]
local function run(a, b, c)
    repeat
        if a then
            break
        end
    until (a or b) and c
    return a, b, c
end

local a, b, c = run(true, false, false)
assert(a == true and b == false and c == false)
local tail_a, tail_b, tail_c = run(false, true, true)
assert(tail_a == false and tail_b == true and tail_c == true)
print("regress_222_shared_short_circuit_dag#1", a, b, c)
a, b, c = run(0, nil, false)
assert(a == 0 and b == nil and c == false)
a, b, c = run(nil, 0, "")
assert(a == nil and b == 0 and c == "")
