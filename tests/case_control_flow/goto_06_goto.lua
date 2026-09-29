-- lua52_02_goto#1: goto基础与标签
-- 单一回边和模拟 continue 应恢复结构化循环，不能将该要求套到后面的不可规约网格。
-- unluac: expect-ast-count [[goto]] [[0]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[goto]] [[0]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[goto]] [[0]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[goto]] [[0]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[goto]] [[0]] [[@proto=6]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[label]] [[0]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[label]] [[0]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[label]] [[0]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[label]] [[0]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[label]] [[0]] [[@proto=6]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[goto]] [[0]] [[@proto=3]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[goto]] [[0]] [[@proto=3]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[goto]] [[0]] [[@proto=3]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[goto]] [[0]] [[@proto=3]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[goto]] [[0]] [[@proto=4]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=3]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=3]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=3]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=3]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=4]] [[@dialect=luajit]]
local function test_goto_label()
    local i = 0

    ::again::
    i = i + 1

    if i < 3 then
        goto again
    end

    assert(i == 3)
    print("lua52_02_goto#1", i)
end

-- lua52_02_goto#2: goto模拟break
local function test_goto_break(limit)
    local outer = 0
    local inner = 0
    local total = 0

    while outer < 4 do
        outer = outer + 1
        local j = 0

        while j < 5 do
            j = j + 1
            inner = inner + 1
            total = total + outer + j

            if total > limit and j > 2 then
                goto done
            end
        end
    end

    ::done::
    print("lua52_02_goto#2", outer, inner, total)
    return outer, inner, total
end

-- lua52_02_goto#3: goto模拟continue
local function test_goto_continue()
    local i = 0
    local kept = 0
    local skipped = 0

    while i < 7 do
        i = i + 1

        if i % 2 == 0 then
            skipped = skipped + i
            goto continue
        end

        kept = kept + i
        if kept > 6 then
            skipped = skipped + 100
        end

        ::continue::
    end

    assert(i == 7 and kept == 16 and skipped == 212)
    print("lua52_02_goto#3", i, kept, skipped)
end

-- lua52_02_goto#4: 不可规约goto网格
local function test_goto_irreducible()
    local x = 0
    local y = 0

    if x == 0 then
        goto left
    end
    goto right

    ::left::
    x = x + 1
    y = y + 10
    if x < 3 then
        goto right
    end
    goto done

    ::right::
    x = x + 2
    y = y + 1
    if y < 13 then
        goto left
    end

    ::done::
    assert(x == 4 and y == 21)
    print("lua52_02_goto#4", x, y)
end

-- lua52_02_goto#5: label合流不能继承单条词法fallthrough的条件事实
local function test_goto_path_condition_merge()
    local function classify(flag, jump)
        local trace = {}
        if jump then
            goto merge
        end
        if flag then
            return "early-true"
        end
        trace[#trace + 1] = "fallthrough"

        ::merge::
        if flag then
            return "merged-true", #trace
        end
        return "false", #trace
    end

    local a, b = classify(false, false)
    local c, d = classify(true, false)
    local e, f = classify(true, true)
    local g, h = classify(false, true)
    assert(a == "false" and b == 1)
    assert(c == "early-true" and d == nil)
    assert(e == "merged-true" and f == 0)
    assert(g == "false" and h == 0)
    print(
        "lua52_02_goto#5",
        classify(false, false),
        classify(true, false),
        classify(true, true)
    )
end

test_goto_label()
local a, b, c = test_goto_break(18)
assert(a == 1 and b == 5 and c == 20)
local d, e, f = test_goto_break(0)
assert(d == 1 and e == 3 and f == 9)
local g, h, i = test_goto_break(100)
assert(g == 4 and h == 19 and i == 101)
local j, k, l = test_goto_break(1000)
assert(j == 4 and k == 20 and l == 110)
test_goto_continue()
test_goto_irreducible()
test_goto_path_condition_merge()
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=6]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[goto]] [[0]] [[@proto=6]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[goto]] [[0]] [[@proto=6]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[goto]] [[0]] [[@proto=6]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[goto]] [[0]] [[@proto=6]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[goto]] [[0]] [[@proto=2]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[label]] [[0]] [[@proto=6]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[label]] [[0]] [[@proto=6]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[label]] [[0]] [[@proto=6]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[label]] [[0]] [[@proto=6]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[label]] [[0]] [[@proto=2]] [[@dialect=luajit]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-ast-count [[while]] [[2]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[repeat]] [[0]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[while]] [[2]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[repeat]] [[0]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[while]] [[2]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[repeat]] [[0]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[while]] [[2]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[repeat]] [[0]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[while]] [[2]] [[@proto=5]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[repeat]] [[0]] [[@proto=5]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=5]] [[@dialect=luajit]]
-- 循环索引的声明留在迭代体，返回准备不能把它外提成额外的共享转存。
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=5]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[assign]] [[4]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[assign]] [[4]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[assign]] [[4]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[assign]] [[4]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[assign]] [[4]] [[@proto=5]] [[@dialect=luajit]]
