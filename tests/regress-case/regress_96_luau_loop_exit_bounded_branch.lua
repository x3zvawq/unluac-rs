-- regress_96_luau_loop_exit_bounded_branch#1: local break must not push the enclosing branch merge to loop exit
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c, xs)
    for _ in xs do
        if a then
            if c then
                break
            end
            while b do
                continue
            end
        end
        if c then
            continue
        end
    end
    return 0
end

print("regress_96_luau_loop_exit_bounded_branch#1", run(false, true, false, {}))
