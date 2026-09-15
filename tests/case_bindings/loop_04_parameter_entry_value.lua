-- regress_143_loop_parameter_entry_value#1: loop 的空 outside defs 仍可能来自函数参数
-- unluac: expect-not-contains [[residual unresolved]]
local function decrement(n)
    for _ = 1, 2 do
        n = n - 1
    end
    return n
end

local result = decrement(5)
assert(result == 3)
print("regress_143_loop_parameter_entry_value#1", result)
