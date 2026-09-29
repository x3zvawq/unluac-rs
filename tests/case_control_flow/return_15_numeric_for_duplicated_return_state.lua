-- regress_86_numeric_for_duplicated_return_state#1: duplicated return exits keep one outer state
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[generic-for]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=1]]
local function run(a, b, xs)
    local x = 0
    if a then
        for _ = 1, 3 do
            while not b do
                for _ in xs do
                    x = x + 1
                    x = x + 1
                    x = x + 1
                end
                if a then
                    continue
                end
            end
            continue
        end
    else
        for _ in xs do
            print("regress_86_numeric_for_duplicated_return_state#1 body", x)
        end
    end
    return x
end

local numeric_result = run(true, true, { true })
local generic_result = run(false, true, { true })
assert(numeric_result == 0 and generic_result == 0)
print("regress_86_numeric_for_duplicated_return_state#1", numeric_result, generic_result)

local saved_print = print
local prints, iterations = 0, 0
print = function(message, value)
    assert(message == "regress_86_numeric_for_duplicated_return_state#1 body" and value == 0)
    prints = prints + 1
end
local function iterator(_, control)
    iterations = iterations + 1
    assert(iterations <= 6, "observed while backedge")
    if control == nil then
        return 1
    end
end
assert(run(nil, false, iterator) == 0 and prints == 1 and iterations == 2)
prints, iterations = 0, 0
assert(run(0, "", iterator) == 0 and prints == 0 and iterations == 0)
assert(not pcall(run, true, false, iterator))
assert(iterations == 7 and prints == 0)
print = saved_print
