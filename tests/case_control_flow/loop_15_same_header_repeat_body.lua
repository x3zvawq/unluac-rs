-- regress_170_same_header_repeat_body#1: outer repeat body 不能阻断 same-header 嵌套 loop 候选
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[while]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, state)
    repeat
        while a do
        end
        if state == 1 then
            state = 2
            break
        elseif state == 2 then
            state = 3
            break
        elseif state == 3 then
            print(state)
        end
        state = 4
    until b
    return state
end

local result = run(false, true, 3)
assert(result == 4)
-- 前移的常量准备不能覆盖 body 仍要读取的 state，break/continue 均观察原值。
assert(run(false, true, 1) == 2)
assert(run(false, true, 2) == 3)
assert(run(false, true, 0) == 4)
print("regress_170_same_header_repeat_body#1", result)

local dispatch = {run}
assert(dispatch[1](false, false, 1) == 2)
assert(dispatch[1](nil, false, 2) == 3)
assert(dispatch[1](nil, 0, nil) == 4)
assert(dispatch[1](false, "", false) == 4)
assert(dispatch[1](false, true, "") == 4)
assert(dispatch[1](false, true, 4) == 4)
-- 参数本身承接全部状态更新，不需要另造跨 repeat 的常量载体。
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- SETLIST buffer 与后续 assert 复用原槽，构造器之后不应留下独立 COPY holder。
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=0]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=0]]
-- unluac: expect-ast-count [[call]] [[21]] [[@proto=0]]
-- 各状态判断、原参数写回和打印保留；Luau 原编译器将两个退出发为 return。
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[0]] [[@dialect=luau]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[2]] [[@dialect=lua5.1]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[2]] [[@dialect=lua5.2]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[2]] [[@dialect=lua5.3]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[2]] [[@dialect=lua5.4]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[2]] [[@dialect=lua5.5]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[2]] [[@dialect=luajit]] [[@proto=1]]
