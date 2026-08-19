-- regress_318_lua51_nested_break_loop_owner: 内层恒真 guard 的 break 不能把回边放到循环 containment 之外
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local issue17_loop = true
while issue17_loop do
    if 2 > 1 then
        print("regress_318_lua51_nested_break_loop_owner", "body")
        if 2 > 1 then
            break
        end
    end
end
