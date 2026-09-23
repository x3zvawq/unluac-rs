-- 闭包创建与 callee COPY 各自保留原槽，后继构造帧不继承已结束的声明前缀。
-- unluac: expect-contains [[= setmetatable({}, {]]
-- unluac: expect-contains [[local result = -get() and "yes" or "no"]] [[@debug=retained]]
-- Luau 常量传播删掉 marker 比较，但保留比较前的 false 写；and true 重发该协议。
-- unluac: expect-count [[and true]] [[1]] [[@dialect=luau]]
do
    local object = {read = function() return "old" end}
    local previous = object.read()
    local marker = 1
    assert(previous == "old" and marker == 1)
    print(previous)
end
do
    local count = 0
    local value = setmetatable({}, {
        __unm = function()
            count = count + 1
            return true
        end,
    })
    local gets = 0
    local function get()
        gets = gets + 1
        return value
    end
    local result = (-get()) and "yes" or "no"
    assert(gets == 1 and count == 1 and result == "yes")
    print(count, gets, result)
end
print("capture_18_closure_callee_copy_frame", "OK")
