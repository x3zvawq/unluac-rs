-- regress_188_luau_nan_fixed_point#1: NaN 常量不能让无改动 pass 误报 changed
-- unluac: expect-contains [[(0/0)]]
-- unluac: expect-not-contains [[unluac error]]

local nan = 0 / 0
assert(nan ~= nan)
print("regress_188_luau_nan_fixed_point#1", nan)
