-- regress_397_generic_for_exact_tail_arity: exact call results must not become an open generic-for pack
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-min [[generic-for]] [[1]]
-- unluac: expect-ast-min [[break]] [[1]]

local function factory()
    return next, { x = 1 }, nil, "extra"
end

local iterator, state = factory()
for key, value in iterator, state do
    break
end

print("regress_397_generic_for_exact_tail_arity", "OK")
