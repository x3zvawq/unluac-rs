-- regress_100_adjacent_loop_redefining_header_state#1: 后继 loop header 重定义变量时仍要继承入口 state
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- 同一状态贯穿两个循环，以绑定数量检查交接，不依赖自动名称编号。
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[2]] [[@proto=1]]
local function run(a)
    local x = 0
    for _ = 1, 3 do
        x = x + 1
    end
    repeat
        x = x + 1
    until a
    return x
end

local result = run(true)
assert(result == 4)
-- a 为假时 repeat 不终止；有限输入只有真值路径，不把该路径算作运行覆盖。
assert(run(0) == 4 and run("") == 4)
print("regress_100_adjacent_loop_redefining_header_state#1", result)
