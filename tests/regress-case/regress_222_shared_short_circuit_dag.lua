-- regress_222_shared_short_circuit_dag#1: 多前驱的共享条件节点仍属于短路 DAG
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
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
print("regress_222_shared_short_circuit_dag#1", a, b, c)
