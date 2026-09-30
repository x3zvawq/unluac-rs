-- regress_360_multi_nil_allocation_root: 并行 nil overwrite 必须终止每个已逃逸 allocation 的物理 root
-- unluac: expect-ast-max [[local-binding]] [[7]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-count [[return nil, nil,]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=2]]
-- unluac: expect-max-count [[local ]] [[5]]

local weak = setmetatable({}, { __mode = "v" })

local function check()
    collectgarbage("collect")
    collectgarbage("collect")
    return weak[1] ~= nil, 73
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

-- 固定 nil 前缀不能截断开放尾包，也不能丢掉 nil 对返回宽度的贡献。
assert(select("#", run()) == 4)
assert(select(4, run()) == 73)
