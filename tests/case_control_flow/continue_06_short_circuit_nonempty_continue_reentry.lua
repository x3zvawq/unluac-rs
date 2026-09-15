-- regress_268_short_circuit_nonempty_continue_reentry: 非空continue target下，multi-node短路不能回退成会重入consumed header的plain if/else
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[    continue]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c)
    while true do
        if a then
            break
        elseif (b or c) and a then
            print("x")
        end
    end
end

assert(run(true, false, false) == nil)
print("regress_268_short_circuit_nonempty_continue_reentry", type(run))
