-- regress_360_multi_nil_allocation_root: 并行 nil overwrite 必须终止每个已逃逸 allocation 的物理 root
-- unluac: expect-ast-max [[local-binding]] [[7]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-count [[return nil, nil,]] [[1]]

local weak = setmetatable({}, { __mode = "v" })

local function check()
    collectgarbage("collect")
    collectgarbage("collect")
    return weak[1] ~= nil
end

local function run()
    do
        local value = {}
        weak[1] = value
        assert(weak[1] ~= nil)
    end
    return nil, nil, check()
end

local first, second, alive = run()
assert(first == nil and second == nil and alive == false)
