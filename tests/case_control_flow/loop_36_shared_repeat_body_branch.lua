-- 内层入口两臂都留在内层；break pad 与正常完成均先进入外层尾条件。
-- unluac: expect-ast-min [[repeat]] [[2]] [[@dialect=luau]] [[@proto=1]]
-- unluac: expect-ast-max [[goto]] [[0]] [[@dialect=luau]]
local else_count = 0
local function run(a, b, c, d)
    repeat
        repeat
            if b then
                if c then break else
                    else_count = else_count + 1
                    print("regress_644#1", "else")
                end
            end
        until d
    until a
end

-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=1]]

-- 经表调用保留待测函数的执行，避免 O2 只执行已内联的常量调用结果。
local callbacks = {run}
for mode = 0, 2 do
    print("regress_644#1", "mode", mode)
    callbacks[1](true, mode ~= 0, mode == 1, true)
    assert(else_count == (mode == 2 and 1 or 0))
end
-- false d 只能经真实 break 终止；其它组用非布尔真值观察两个尾条件。
callbacks[1](0, false, false, "")
callbacks[1]("", 0, 0, nil)
assert(else_count == 1)
callbacks[1]({}, true, false, 0)
assert(else_count == 2)
callbacks[1](0, "", nil, "")
assert(else_count == 3)
callbacks[1](true, true, true, false)
callbacks[1](true, nil, true, 0)
assert(else_count == 3)

-- 共享 body 只保留一次状态写和一次输出；外围驱动不引入额外状态更新。
-- unluac: expect-ast-count [[assign]] [[1]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[call]] [[14]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=0]]
