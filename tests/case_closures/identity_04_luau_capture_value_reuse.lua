-- regress_219_luau_capture_value_reuse#1: CAPTURE VAL 必须与后续物理寄存器复用隔离
-- unluac: expect-not-contains [[unluac error]]
-- 捕获快照、返回闭包和后续结果各保留一个身份；参数与 callee 准备不额外声明。
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=1]]
-- 展开体整体归还工厂调用，根函数只保留工厂与两个独立返回闭包。
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=0]]
local function build(input)
    local reader

    do
        local captured = tostring(input)
        reader = function()
            return captured
        end
    end

    do
        local replacement = tostring(input + 18)
        print("replacement", replacement)
    end

    return reader
end

local reader = build(11)
assert(reader() == "11")
print("regress_219_luau_capture_value_reuse#1", reader())

-- 第二次展开复用工厂模板，但不能复用第一次捕获的值或闭包对象。
local other = build(-7)
assert(other() == "-7" and reader() == "11")
assert(reader ~= other)
print("regress_219_luau_capture_value_reuse#2", other(), reader())
