-- regress_317_lua51_loop_region_ownership: 短路 if 的 else 数值循环不能把退出边归给外层分支
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-contains [[if not (issue17_a or issue17_b) then]]
-- unluac: expect-not-contains [[repeat]]
-- unluac: expect-not-contains [[break]]
if issue17_a or issue17_b then
    local unused
else
    for index = 1, 2 do
    end
end

print("regress_317_lua51_loop_region_ownership", "done")
