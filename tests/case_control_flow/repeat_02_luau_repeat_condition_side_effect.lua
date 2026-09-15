-- regress_125_luau_repeat_condition_side_effect#1: repeat 条件前的副作用不能被伪造的 continue 跳过
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[print]]
-- unluac: expect-not-contains [[continue]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
return function(c, a, b, t)
    local x = 0
    for _ in t do
        repeat
            if c then
                print(x)
            else
                if not a or not b then
                    x += 1
                    print(x)
                    if x < 3 then
                        break
                    end
                end
            end
            print(x)
        until c
    end
    return x
end
