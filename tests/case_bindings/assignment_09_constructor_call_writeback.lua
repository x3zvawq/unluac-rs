-- 构造器参数属于完整 CALL+MOVE：被调用函数观察旧 cell，返回后才安装新对象。
-- unluac: expect-contains [[current = install({]] [[@debug=retained]]
-- unluac: expect-not-contains [[= assert]] [[@dialect=luau]]
local function exercise()
    local current = {tag = "old", reads = 0}
    local function observe()
        current.reads = current.reads + 1
        return current
    end
    local function install(value)
        assert(observe().tag == "old")
        assert(current.reads == 1)
        assert(value.read() == current)
        return value
    end
    current = install({tag = "new", reads = 0, read = function() return current end})
    assert(observe() == current and current.read() == current)
    assert(current.reads == 1)
    return current.tag
end
assert(exercise() == "new")
print("assignment_09_constructor_call_writeback", "OK")
