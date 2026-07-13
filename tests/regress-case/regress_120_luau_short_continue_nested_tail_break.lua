-- regress_120_luau_short_continue_nested_tail_break#1: 短路 continue 后的 nested repeat 与 tail break 保持独立 owner
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
return function(a, b, c, xs)
    local x = 0
    for i = 1, 3 do
        x = x + 1
        repeat
            if a then
                if xs[x] then break end
                if a then continue else x = x + 1 end
            else
                while b do
                    x = x + 1
                    x = x + 1
                end
                for k, v in xs do
                    x = x + 1
                end
                if a or c then continue end
            end
            repeat
                for k, v in xs do
                    x = x + 1
                    x = x + 1
                end
            until not b
            if a and b then break end
        until a
    end
    return x
end
