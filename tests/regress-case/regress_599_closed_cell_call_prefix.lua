-- 已关闭的循环 cell 不属于循环后调用的活动声明前缀。
-- unluac: expect-ast-min [[numeric-for]] [[1]]
local function closed_prefix()
    local readers = {}
    for index = 1, 2 do
        local value = index
        readers[index] = function() return value end
        value = value + 10
    end
    assert(readers[1]() == 11 and readers[2]() == 12)
end

-- callee 来自紧邻的同槽 CALL；闭包仍需在第二次调用前保持活跃。
local function build()
    local result
    do
        local value = 1
        result = function() return value end
        value = 2
    end
    return result
end
closed_prefix()
assert(build()() == 2)
