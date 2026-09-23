-- regress_318_lua51_nested_break_loop_owner: 内层恒真 guard 的 break 不能把回边放到循环 containment 之外
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-count [[if 1 < 2 then]] [[2]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[break]] [[1]]
local issue17_loop = true
while issue17_loop do
    if 2 > 1 then
        print("regress_318_lua51_nested_break_loop_owner", "body")
        if 2 > 1 then
            break
        end
    end
end
