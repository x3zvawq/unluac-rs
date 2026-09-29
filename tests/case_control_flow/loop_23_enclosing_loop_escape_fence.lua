-- regress_257_enclosing_loop_escape_fence: enclosing while 的 break 不能伪装 single-pass fence
-- unluac: expect-contains [[while]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

local function run(flags, limit)
    local i = 0
    while i < limit do
        if flags[1] then
            i = i + 0
        elseif flags[2] then
            if flags[3] then break end
        end
        i = i + 0
        if flags[4] then
            i = i + 0
        elseif flags[5] then
            if flags[6] then break end
        end
        i = i + 0
        i = i + 1
    end
    return i
end

assert(run({}, 2) == 2)
assert(run({false, true, true}, 2) == 0)
assert(run({false, false, false, false, true, true}, 2) == 0)
print("regress_257_enclosing_loop_escape_fence")

for pattern = 0, 63 do
    local flags, bits = {}, pattern
    for bit = 1, 6 do
        flags[bit] = bits % 2 == 1
        bits = math.floor(bits / 2)
    end
    local exits = (not flags[1] and flags[2] and flags[3])
        or (not flags[4] and flags[5] and flags[6])
    assert(run(flags, 2) == (exits and 0 or 2))
end
assert(run({0, true, true, 0, true, true}, 2) == 2)
assert(run({}, 0) == 0)
assert(run({}, -2) == 0)
assert(run({}, 2.5) == 3)
-- 第二轮从第一组分支退出；被短路的 flag 和第二组条件都不能提前读取。
local reads, pass = {}, 0
local changing = setmetatable({}, {__index = function(_, key)
    reads[#reads + 1] = key
    if key == 1 then
        pass = pass + 1
        return pass == 1
    end
    if key == 2 or key == 3 then return true end
    assert(key == 4 or key == 5)
    return false
end})
assert(run(changing, 3) == 1)
assert(table.concat(reads, ",") == "1,4,5,1,2,3")

-- 同一短路值帧中的下一次查表可观察旧结果根；各方言以原源码运行结果为基线。
do
    local function check_lookup_frame()
        local weak = setmetatable({}, {__mode = "v"})
        local trace, mode = {}, 0
        local flags = setmetatable({}, {__index = function(_, key)
            collectgarbage("collect")
            collectgarbage("collect")
            trace[#trace + 1] = key .. ":" .. tostring(weak.value ~= nil)
            if (mode == 1 and key == 1) or (mode == 2 and key == 2)
                or (mode == 4 and key == 6) then
                local value = {}
                weak.value = value
                return value
            end
            if key == 1 then return false end
            if key == 2 then return mode == 3 end
            if key == 3 then
                if mode == 3 then return 0 end
                return false
            end
            if key == 4 then return mode == 2 end
            if key == 5 then return "" end
            assert(key == 6)
            return "done"
        end})
        local function choose(input)
            local value = (not input[1] and input[2] and input[3])
                or (not input[4] and input[5] and input[6])
            return value, value
        end
        for scenario = 1, 4 do
            mode = scenario
            trace = {}
            weak.value = nil
            local first, second = choose(flags)
            assert(first == second)
            if mode == 1 then assert(first == "done") end
            if mode == 2 then assert(first == false) end
            if mode == 3 then assert(first == 0) end
            if mode == 4 then assert(first == weak.value) end
            print("lookup-frame", mode, table.concat(trace, ","))
        end
    end
    check_lookup_frame()
end
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[2]] [[@proto=1]]
-- elseif 在 AST 中计为条件节点，共四个分支条件。
-- unluac: expect-ast-count [[if]] [[4]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]]
-- 四个原始 +0 运算不能按值域推断删掉。
-- unluac: expect-count [[ + 0]] [[4]]
-- 测试期望的短路值不应展开成嵌套分支和额外临时声明。
-- unluac: expect-ast-count [[local-binding]] [[10]] [[@proto=0]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=5]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=5]]
-- 观察器中的模式比较也不应留下额外上值快照声明。
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=4]]
