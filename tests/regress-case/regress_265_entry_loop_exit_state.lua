-- regress_265_entry_loop_exit_state#1: entry-header loop must initialize an all-inside exit phi
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c)
    repeat
        if b then
            while c do
                c = false
            end
            break
        end
        a = true
    until a
    return c
end

print("regress_265_entry_loop_exit_state#1a", run(false, true, true))
print("regress_265_entry_loop_exit_state#1b", run(false, false, true))
