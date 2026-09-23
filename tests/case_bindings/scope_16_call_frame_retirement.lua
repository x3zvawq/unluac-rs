-- 后继调用复用临时对象槽；恢复词法末端后，弱引用观察必须与原 VM 保持一致。
-- unluac: expect-not-contains [[= assert]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-ast-max [[local-binding]] [[8]]
-- unluac: expect-count [[() == ]] [[1]]
-- unluac: expect-contains [[assert(read() == value)]] [[@debug=retained]]
local weak = setmetatable({}, {__mode = "v"})
local allocations, reads = 0, 0
local function make()
    allocations = allocations + 1
    local object = {}
    weak[1] = object
    return object
end
local function exercise(value)
    local function read()
        reads = reads + 1
        if collectgarbage then
            collectgarbage("collect")
            -- FASTCALL 快路径是否覆盖 callee 槽由 VM 决定，比较原程序与生成程序的观察。
            print("scope-root", weak[1] ~= nil)
        end
        return value
    end
    do
        local expired = make()
        assert(expired ~= nil)
    end
    assert(read() == value)
    return value
end
assert(exercise(7) == 7 and exercise(9) == 9)
assert(allocations == 2 and reads == 2)
print("call-frame-retirement", allocations, reads)
