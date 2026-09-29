-- luau_02_vector#1: native vector constant uses the configured host constructor
-- unluac: expect-contains [[vector.create(1.5, -2, 3.25)]]
-- unluac: expect-not-contains [[vector.create(1.5, -2, 3.25, 0]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-max [[local-binding]] [[1]]

local value = vector.create(1.5, -2, 3.25)
assert(value.x == 1.5 and value.y == -2 and value.z == 3.25)
print("luau_02_vector#1", value)
