-- regress_113_luau_short_circuit_outer_break#1: 短路真臂跨内层 for 后退出外层 for
-- unluac: expect-contains [[ or ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c, xs)
    local x = 0
    for _, _ in xs do
        if a or c then
            for i = 1, 3 do
                print(x)
                print(x)
                print(x)
            end
            break
        else
            if a and b then
                x = x + 1
            end
        end
    end
    print(x)
    return x
end

print("regress_113_luau_nested_exit#1", run(false, false, true, { 1, 2 }))
local saved_print = print
local prints = 0
print = function(value)
    assert(value == 0)
    prints = prints + 1
end
local function check(a, b, c, length, expected_calls, expected_prints)
    local calls = 0
    local function iterator()
        calls = calls + 1
        if calls <= length then return calls, calls end
    end
    prints = 0
    assert(run(a, b, c, iterator) == 0)
    assert(calls == expected_calls and prints == expected_prints)
end
local checks = {check}
checks[1](true, false, false, 2, 1, 10)
checks[1](false, true, false, 2, 3, 1)
checks[1](nil, true, 0, 2, 1, 10)
checks[1](0, true, false, 2, 1, 10)
checks[1](false, false, "", 2, 1, 10)
checks[1](true, true, true, 0, 1, 1)
print = saved_print
-- unluac: expect-ast-count [[local-binding]] [[11]]
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]]
