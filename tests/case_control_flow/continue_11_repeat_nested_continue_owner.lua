-- regress_366_repeat_nested_continue_owner: an inner-loop continue does not skip the outer repeat tail condition
-- unluac: expect-contains [[until mark("stop", true) or mark("again", false)]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=0]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=0]] [[@variant=O0]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=0]] [[@variant=O1]]
-- unluac: expect-ast-count [[numeric-for]] [[0]] [[@proto=0]] [[@variant=O2]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=2]]
-- 两次 mark 在原同槽准备和求值；首个谓词不应留下 callee/比较结果声明。
-- unluac: expect-ast-count [[repeat-condition-local]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[unresolved]]

local events = {}

function mark(name, value)
    events[#events + 1] = name
    return value
end

repeat
    for index = 1, 2 do
        if index == 1 then
            continue
        end
        events[#events + 1] = "inner"
    end
    if mark("stop", true) then
        break
    end
until mark("again", false)

assert(table.concat(events, ",") == "inner,stop")

-- 外层条件分别从 stop、again 退出，并实际经过回边；两者同轮为真时
-- stop 必须短路 again。内层 continue 仍只跳过 index=1 的正文。
local function run(stop_at, again_at)
    local iterations = 0
    repeat
        iterations = iterations + 1
        assert(iterations <= 3)
        for index = 1, 2 do
            if index == 1 then
                continue
            end
            events[#events + 1] = "inner"
        end
        if mark("stop", iterations == stop_at) then
            break
        end
    until mark("again", iterations == again_at)
    return iterations
end

events = {}
assert(run(1, 3) == 1)
assert(table.concat(events, ",") == "inner,stop")
events = {}
assert(run(3, 1) == 1)
assert(table.concat(events, ",") == "inner,stop,again")
events = {}
assert(run(3, 3) == 3)
assert(table.concat(events, ",") == "inner,stop,again,inner,stop,again,inner,stop")
events = {}
assert(run(3, 2) == 2)
assert(table.concat(events, ",") == "inner,stop,again,inner,stop,again")
print("nested continue conditions", table.concat(events, ","))

-- 第一次谓词可以替换全局 callee；短路失败后的第二次调用必须重新读取它。
local original_mark = mark
mark = function(name, value)
    local result = original_mark(name, value)
    if name == "stop" then
        mark = function(next_name, next_value)
            events[#events + 1] = "reloaded"
            return original_mark(next_name, next_value)
        end
    end
    return result
end
events = {}
assert(run(3, 1) == 1)
assert(table.concat(events, ",") == "inner,stop,reloaded,again")
mark = original_mark
