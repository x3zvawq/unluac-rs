-- 新 CLOSE 窗口的只读捕获不继承旧 CALL 结果；旧声明段与新构造器参数须一起恢复原帧。
-- unluac: expect-contains [[= setmetatable({}, {]]
-- unluac: expect-ast-count [[do-block]] [[2]]
-- unluac: expect-not-contains [[read = 0]]
-- unluac: expect-contains [[.answer = 3]]
do
    local object = {read = function() return "old" end}
    local previous = object.read()
    assert(previous == "old")
    print(previous)
end
do
    local writes = 0
    local value = setmetatable({}, {
        __newindex = function(_, key, item)
            assert(key == "answer")
            writes = writes + item
        end,
    })
    local function reader()
        value.answer = 4
        assert(writes == 7)
        return value
    end
    value.answer = 3
    assert(writes == 3)
    SAVED_READER = reader
end
SAVED_READER()
SAVED_READER = nil
print("capture_17_closed_cell_frame", "OK")
