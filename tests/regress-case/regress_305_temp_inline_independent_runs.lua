-- regress_305_temp_inline_independent_runs: 独立 callee/materialization run 必须在同轮批量收敛
local calls = 0
local values = {
    function()
        calls = calls + 1
        return 1
    end,
}

assert(values[1]() == 1 and values[2] == nil)
assert(values[1]() == 1 and values[2] == nil)
assert(values[1]() == 1 and values[2] == nil)
print("regress_305_temp_inline_independent_runs", calls)
