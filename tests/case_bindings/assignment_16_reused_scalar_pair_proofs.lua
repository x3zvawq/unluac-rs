-- 重复快照共享相同写回合同，两个低槽目标和调用时点均保持原序。
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[assign]] [[2]] [[@proto=2]]
-- unluac: expect-ast-count [[call]] [[2]] [[@proto=2]]
local expected_owner = {}
local calls = 0
scalar_pair_observe = function(owner, value)
    assert(owner == expected_owner)
    calls = calls + 1
    assert(value == 7)
end

local function repeated(owner)
    local value
    owner, value = owner, 7
    scalar_pair_observe(owner, value)
    owner, value = owner, 7
    scalar_pair_observe(owner, value)
    return owner, value
end

local owner, value = repeated(expected_owner)
assert(owner == expected_owner and value == 7 and calls == 2)
scalar_pair_observe = nil
print("reused-scalar-pair-proofs", "OK")
