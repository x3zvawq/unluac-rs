-- regress_128_same_header_plain_nested_loops#1: 普通 while/repeat 共用 header 时仍是两个严格嵌套 loop
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
return function(a, b)
    repeat
        while a do
            if b then
                break
            end
        end
    until b
end
