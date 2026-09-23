-- regress_305_temp_inline_independent_runs: 独立 callee/materialization run 必须在同轮批量收敛
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=0]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=0]]
-- unluac: expect-count [[assert(]] [[4]]
-- unluac: expect-count [[assert(values[1]() == 1 and values[2] == nil)]] [[3]] [[@debug=retained]]
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
assert(calls == 3)
print("regress_305_temp_inline_independent_runs", calls)
