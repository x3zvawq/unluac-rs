-- regress_107_luau_linear_break_exit_pad#1: O2 展开的独占线性块属于同一个 break exit pad
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- 展开后的三个 print 留在提前退出臂；尾条件保留原判断，不制造 normal-tail 标记。
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=1]]
-- unluac: expect-not-contains [[until false]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, xs)
    for k, v in xs do
        repeat
            if a then
                for i = 1, 3 do
                    print(k, v)
                    continue
                end
                break
            else
                for i = 1, 3 do
                    print(k, v)
                    print(k, v)
                end
            end
        until a
    end
end

-- a=false 且迭代器非空时原循环不终止；有限路径必须实际执行 O2 展开的三次 print。
local calls = 0
run(true, function()
    calls = calls + 1
    if calls == 1 then return "key", "value" end
end)
assert(calls == 2)
run(false, {})
print("regress_107_luau_linear_break_exit_pad#1")
