-- unluac: expect-contains [[print("after-window", next())]]
-- Phi 声明与 Def 声明共同拥有 debug 窗口；不能丢掉 do 后让后继调用新增载体。
local function factory(...)
    local value = ...
    return function() return value end
end
do
    local first = factory(1)
    local second = factory(2)
    local same = first == second
    assert(not same)
    print("phi-window", same)
end
do
    local next = factory(3)
    print("after-window", next())
end
