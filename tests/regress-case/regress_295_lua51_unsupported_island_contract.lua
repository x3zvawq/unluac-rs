-- regress_295_lua51_unsupported_island_contract: 测试框架会把标记的跳转改写成
-- Lua 5.1 源码无法产生的双入口循环，用于验证 strict/permissive 的最终计划门禁。
local x = 0
if _G.enter_body then
    x = x + 0
else
    x = x + 0
end
while x < 4 do
    if x == 1 then
        x = x + 1
    else
        x = x + 2
    end
end
print("regress_295_lua51_unsupported_island_contract", x)
