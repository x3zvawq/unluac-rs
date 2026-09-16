-- Original regression by ItsLucas <itslucas@itslucas.me>, PR #35.
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]
-- HIR can eliminate a contradictory branch after StructurePlan recorded a goto.
-- unluac: expect-not-contains [[unluac error]]
local function check(a, b)
    if a then
        if a then
        else
            if a or b then
                impossible = impossible + 6
            end
        end
    end
end
for i = 0, 3 do
    check(i % 2 == 1, i >= 2)
end
print("stale-transfer", "ok")
