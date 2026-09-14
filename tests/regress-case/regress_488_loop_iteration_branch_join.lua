-- regress_488_loop_iteration_branch_join: a next-iteration postdom is not this iteration's branch join
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-ast-min [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-min [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-min [[break]] [[1]] [[@proto=1]]
local function run(a, b, c)
    local x = 0
    repeat
        if a then
            repeat
                x = x + 1
            until b
            if c then
                break
            end
        end
        while not b do
            x = x + 1
        end
    until false
    return x
end

-- Only this stable-parameter combination terminates; keep the other CFG routes for compilation.
assert(run(true, true, true) == 1)
assert(run(1, "ready", {}) == 1)
print("regress_488_loop_iteration_branch_join", "closed")
