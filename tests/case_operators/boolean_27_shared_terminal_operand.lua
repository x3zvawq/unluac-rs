-- 两条 Boolean 写入经过透明合流 pad，再作为外层比较的操作数。
-- 共享终边不能把路径上的 true/false 降成尚未物化的内部 phi。
-- unluac: expect-count [[ = p1_1 == 1]] [[1]] [[@dialect=luau]] [[@debug=stripped]]
-- O2 可以复制内联函数体；debug 名称下只要求比较值确实写入其结果。
-- unluac: expect-contains [[expected = selected == 1]] [[@dialect=luau]] [[@debug=retained]]
-- 捕获发生前完成的比较 initializer 不应逐轮分裂为空声明和赋值。
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=0]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=0]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=0]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=0]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=0]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=0]] [[@dialect=luajit]]
-- 内嵌取值写回原结果，比较直接赋值；不为两层值各制造空的中转声明。
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=3]] [[@dialect=luajit]]
-- 入口 Boolean 预写属于被捕获的结果初始化，不应独占一个声明并挤散后续调用帧。
-- unluac: expect-ast-max [[local-binding]] [[6]] [[@proto=0]] [[@dialect=luau]] [[@variant=O0]] [[@debug=stripped]]
-- unluac: expect-ast-max [[local-binding]] [[6]] [[@proto=0]] [[@dialect=luau]] [[@variant=O1]] [[@debug=stripped]]
-- O2 展开的三次检查保留原初始化与返回值，但不为条件取值重复快照左操作数。
-- unluac: expect-ast-max [[local-binding]] [[21]] [[@proto=0]] [[@dialect=luau]] [[@variant=O2]] [[@debug=stripped]]
local function check(enabled, selected, flag, read, calls)
    local saved = flag
    local first, second
    local actual = read()
    local expected
    if enabled == 1 or enabled >= 3 then
        expected = selected == 1
    else
        expected = saved
    end
    second = actual == expected
    first = second
    if second then
        first = calls == 3
    end
    local result = first
    return result
end

for enabled = 0, 4 do
    for selected = 0, 2 do
        local flag = enabled == 1 or enabled >= 3
        local reads = 0
        local function read()
            reads = reads + 1
            return flag and selected == 1
        end
        assert(check(enabled, selected, flag, read, 3))
        assert(not check(enabled, selected, flag, read, 2))
        assert(not check(enabled, selected, flag, function() return not read() end, 3))
        assert(reads == 3)
    end
end
print("shared-terminal-operand", "ok")
