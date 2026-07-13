-- regress_129_lua51_nonempty_backedge_pad#1: 回边赋值属于 while body，不是 repeat 条件 pad
-- unluac: expect-contains [[while true do]]
-- unluac: expect-contains [[return 1]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function f(a, b)
    while true do
        print("regress_129_lua51_nonempty_backedge_pad#1 tick")
        if a then
            break
        end
        if b then
            return 1
        end
        a = true
    end
    return 2
end

print("regress_129_lua51_nonempty_backedge_pad#1", f(false, false))
