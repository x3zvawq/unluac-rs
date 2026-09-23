-- body 末尾布尔值合流后的 Close/JMP 是正常迭代尾，不能误认为跳过 body 的 continue。
-- unluac: expect-ast-min [[numeric-for]] [[2]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=0]]
local function invoke(callback)
    return callback()
end

local function collect(limit)
    local getters = {}
    for index = 1, limit do
        local trace = ""
        local actual = invoke(function()
            trace = trace .. "x"
            return index
        end)
        getters[index] = function() return index, trace end
        assert(rawequal(actual, index) and trace == "x")
    end
    return getters
end

assert(next(collect(0)) == nil)
local getters = collect(3)
for index = 1, 3 do
    local actual, trace = getters[index]()
    assert(actual == index and trace == "x")
end
print("regress_563_loop_tail_capture_cleanup", "OK")
