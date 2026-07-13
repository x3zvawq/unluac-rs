-- regress_142_loop_multi_exit_downstream_value_merge#1: 多个 break pad 的共同 merge 必须继承 loop live-out
-- unluac: expect-not-contains [[residual unresolved]]
local x = 0

while true do
    if x > 5 then
        break
    end
    x = x + 1
    if x == 4 then
        break
    end
end

print("regress_142_loop_multi_exit_downstream_value_merge#1", x)
