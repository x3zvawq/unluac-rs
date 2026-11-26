-- regress_188_luau_nan_fixed_point#1: NaN 常量不能让无改动 pass 误报 changed
-- unluac: expect-contains [[(0/0)]]

local nan = 0 / 0
assert(nan ~= nan)
local function observe(value)
    return value ~= value and not (value < 0) and not (value > 0)
        and not (value <= 0) and not (value >= 0)
end
assert(observe(nan) and not observe(0))
print("regress_188_luau_nan_fixed_point#1", nan)
