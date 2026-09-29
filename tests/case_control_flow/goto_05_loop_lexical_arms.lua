-- common_14_loop_lexical_arms#1: while 正文的纯 return arm 保持在词法循环内
local function test_return_arm()
    local function run(flag)
        local turns = 0
        while turns < 3 do
            turns = turns + 1
            if flag then
                return turns
            end
        end
        return turns
    end

    assert(run(true) == 1 and run(false) == 3)
    assert(run(nil) == 3 and run(0) == 1 and run("") == 1)
    print("common_14_loop_lexical_arms#1", run(true), run(false))
end

-- common_14_loop_lexical_arms#2: while 后的闭合循环不能被收进前一个 loop body
local function test_closed_sibling()
    local function run(enter)
        local turns = 0
        while enter do
            turns = turns + 1
            enter = false
        end
        while true do
            if turns >= 0 then
                return turns
            end
        end
    end

    assert(run(true) == 1 and run(false) == 0)
    assert(run(nil) == 0 and run(0) == 1 and run("") == 1)
    print("common_14_loop_lexical_arms#2", run(true), run(false))
end

test_return_arm()
test_closed_sibling()
-- 含纯 return 的循环臂应由结构化控制表达。
-- unluac: expect-ast-max [[goto]] [[0]] [[@proto=2]] [[@dialect=lua5.1]]
-- unluac: expect-ast-max [[goto]] [[0]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-max [[goto]] [[0]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-max [[goto]] [[0]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-max [[goto]] [[0]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-max [[goto]] [[0]] [[@proto=2]] [[@dialect=luau]]
-- unluac: expect-ast-max [[goto]] [[0]] [[@proto=4]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=2]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=2]] [[@dialect=luau]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=4]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[while]] [[2]] [[@proto=4]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[while]] [[2]] [[@proto=4]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[while]] [[2]] [[@proto=4]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[while]] [[2]] [[@proto=4]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[while]] [[2]] [[@proto=4]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[while]] [[2]] [[@proto=4]] [[@dialect=luau]]
-- unluac: expect-ast-count [[while]] [[2]] [[@proto=2]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-not-contains [[unresolved]]
