-- regress_105_luau_same_header_loop_path_owner#1: 按入口区分共享 header 的 numeric-for 与 while
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, xs)
    local x = 0
    repeat
        if a then
            if xs[x] then
                continue
            end
            for i = 1, 3 do
                while b do
                    x = x + 1
                end
            end
        end
        if a and b then
            break
        end
    until a
    return x
end

-- 该 proto 可能不终止；只验证结构恢复，不在测试入口调用。
print("regress_105_luau_same_header_loop_path_owner#1")
