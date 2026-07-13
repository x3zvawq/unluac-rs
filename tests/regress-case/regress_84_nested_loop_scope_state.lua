-- regress_84_nested_loop_scope_state#1: nested repeat remains in the outer for body and shares state
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[until]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, xs)
    local x = 0
    for _ in xs do
        print("regress_84_nested_loop_scope_state#1 body", x)
        if a and b then
            repeat
                for _ in xs do
                    x = x + 1
                end
            until xs[x]
            break
        end
    end
    return x
end

print("regress_84_nested_loop_scope_state#1", run(true, true, { true }))
