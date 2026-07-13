-- regress_122_luau_same_header_loop_break_owner#1: same-header loop 的条件 header 不被前置短路吞并
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[continue]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
return function(a, b, xs)
    repeat
        repeat
            for k, v in xs do
                print(k, v)
            end
        until not b
        if a and b then break end
    until a
    return true
end
