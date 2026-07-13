-- regress_124_luau_loop_break_header_phi_owner#1: nested break branch 的入口 phi 继承 active loop state owner
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
return function(a, b, t)
    local x = 0
    for _ in t do
        repeat
            if a then
                while b do
                    x += 1
                end
            else
                if not a or not b then
                    x += 1
                    if b then
                        break
                    end
                end
            end
            x += 0
        until a
    end
    return x
end
