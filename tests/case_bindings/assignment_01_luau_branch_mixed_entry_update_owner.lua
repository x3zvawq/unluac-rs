-- regress_115_luau_branch_mixed_entry_update_owner#1: BVM 混合 preserved/update 路径继承 state owner
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function nested(a, b, c, xs)
    local x = 0
    if a then
        repeat
            for k, v in xs do
                if c then
                    print(x)
                else
                    x = x + 1
                end
            end
        until c
        if b then
            print(x)
        else
            if a then
                x = x + 1
            end
            while not b do
                for k, v in xs do
                    x = x + 1
                end
                if c then
                    continue
                else
                    x = x + 1
                    break
                end
            end
        end
    else
        x = x + 1
    end
    return x
end

print("regress_115_luau_branch_mixed_entry_update_owner#1", nested(true, true, true, {}))
