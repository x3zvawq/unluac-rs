-- 字段闭包在原空闲槽创建；安装回调与后续调用共享同一个可变捕获 cell。
-- unluac: expect-ast-count [[local-function]] [[2]]
-- unluac: expect-contains [[= setmetatable({}, {]]
-- unluac: expect-not-contains [[ = assert]]
-- unluac: expect-not-contains [[ = print]]
local target
local installed
local writes = 0
local function install(value)
    local current = value
    target.field = function(delta)
        current = current + delta
        return current
    end
    current = current + 1
    return current
end

local function direct(target, value)
    local current = value
    target.field = function(delta)
        current = current + delta
        return current
    end
    current = current + 1
    return current
end

target = setmetatable({}, {
    __newindex = function(_, key, value)
        assert(key == "field")
        writes = writes + 1
        installed = value
        assert(value(2) == 12)
    end,
})
assert(install(10) == 13)
assert(writes == 1 and installed(1) == 14)
assert(direct(target, 10) == 13)
assert(writes == 2 and installed(1) == 14)
print("closure field", writes, installed(3))
