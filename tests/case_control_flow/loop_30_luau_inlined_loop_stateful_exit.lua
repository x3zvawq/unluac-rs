-- regress_291_luau_inlined_loop_stateful_exit: O2内联loop的normal-only出口不能提前执行
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[--!optimize 2]]
-- unluac: expect-instruction-count [[call]] [[15]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

local calls = {}

local function hit()
    table.insert(calls, "hit")
    return nil
end

local function miss()
    table.insert(calls, "miss")
    return false
end

local function any(a)
    for i = 1, #a do
        if a[i] then
            return hit()
        end
    end
    return miss()
end

-- 命中前先跨过一次 falsy，命中后不能继续访问下一项；正常出口须遍历完两项。
local first = any({ false, true, true })
local second = any({ false, false })
assert(first == nil, first)
assert(second == false, second)
assert(table.concat(calls, ",") == "hit,miss", table.concat(calls, ","))
print("regress_291_luau_inlined_loop_stateful_exit", table.concat(calls, ","))
-- 完整展开体恢复为现存 any 的调用；强制 O2 内联后仍保持原 CALL 数量。
-- 根函数只保留 calls、三个原函数和两个结果；退出标志和调用准备不成为源码绑定。
-- unluac: expect-count [[= 1, #]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=0]]
-- unluac: expect-ast-count [[numeric-for]] [[0]] [[@proto=0]]
-- unluac: expect-ast-count [[break]] [[0]] [[@proto=0]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=3]]
