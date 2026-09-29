-- regress_119_luau_repeat_continue_pad_owner#1: repeat 的透明 continue pad 由分支臂消费
-- unluac: expect-contains [[repeat]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[0]] [[@proto=1]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(b)
    repeat
        while not b do break end
    until b
    return true
end

-- 表调用避免 O2 将 run(true) 内联为字面量，确保实际运行被测函数。
-- false/nil 输入的原函数不终止；此处不把它改成有界循环。
local dispatch = {run}
for _, value in ipairs({true, 0, ""}) do
    local result = dispatch[1](value)
    assert(result == true)
    print("regress_119_luau_repeat_continue_pad_owner#1", value, result)
end
