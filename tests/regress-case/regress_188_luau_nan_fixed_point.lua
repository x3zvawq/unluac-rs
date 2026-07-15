-- regress_188_luau_nan_fixed_point#1: NaN 常量不能让无改动 pass 误报 changed
-- unluac: expect-contains [[(0/0)]]
-- unluac: expect-not-contains [[unluac error]]

print("regress_188_luau_nan_fixed_point#1", 0 / 0)
