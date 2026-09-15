-- regress_148_luau_repeat_recompile_state_owner#1: repeat 再编译后的中间 phi 继续归外层 loop state
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
return function(a, b, c, xs)
    local x = 0
    for _ in xs do
        repeat
            if a then
                print(x)
            elseif not b or not c then
                x = x + 1
                print(x)
                if x < 3 then
                    break
                end
            end
            print(x)
        until a
    end
    return x
end
