-- regress_156_numeric_for_binding_inner_loop#1: 同header内层while复用numeric-for binding owner
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[            r1_2 = r1_1]]
local function run(limit)
    local total = 0
    for index = 1, limit do
        while index < 2 do
            index = index + 1
        end
        total = total + index
    end
    return total
end

print("regress_156_numeric_for_binding_inner_loop#1", run(2))
