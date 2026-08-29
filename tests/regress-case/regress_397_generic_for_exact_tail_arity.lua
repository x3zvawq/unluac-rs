-- regress_397_generic_for_exact_tail_arity: exact call results must not become an open generic-for pack
-- unluac: expect-not-contains [[unluac error]]

local function factory()
    return next, { x = 1 }, nil, "extra"
end

local iterator, state = factory()
for key, value in iterator, state do
    break
end

print("regress_397_generic_for_exact_tail_arity", "OK")
