-- luau_02_vector#1: native vector constant uses the configured host constructor
-- unluac: expect-contains [[vector.create(1.5, -2, 3.25)]]
-- unluac: expect-not-contains [[vector.create(1.5, -2, 3.25, 0]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

local value = vector.create(1.5, -2, 3.25)
print("luau_02_vector#1", value)
