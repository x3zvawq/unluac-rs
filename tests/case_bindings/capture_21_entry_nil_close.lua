-- Entry nil cell 必须在原 CLOSE 窗口内先声明，后续复用同槽的构造器不能被旧前缀抬高。
-- unluac: expect-contains [[= setmetatable({}, {]]
-- unluac: expect-not-contains [[unresolved]]
-- 入口 cell 可以没有初始化值；同槽后继多返回声明必须完整恢复，不能再拆空声明。
-- unluac: expect-ast-max [[empty-local]] [[1]] [[@proto=0]]
do
    local cell
    local value = {}
    local function write(next_value)
        cell = next_value
    end
    assert(cell == nil)
    write(value)
    assert(cell == value, "Entry reads must observe writes through the captured cell")
    write(false)
    assert(cell == false)
    print("entry-nil-close", cell == false)
end

do
    local shared = 21
    local function values()
        return shared, shared + 1
    end
    local first, second = values()
    assert(first == 21 and second == 22)
    print("closed-result-prefix", first, second)
end

do
    local calls = 0
    local value = setmetatable({}, {
        __index = function(_, key)
            calls = calls + 1
            return key
        end,
    })
    assert(value.answer == "answer" and calls == 1)
    print("reused-prefix", calls)
end
