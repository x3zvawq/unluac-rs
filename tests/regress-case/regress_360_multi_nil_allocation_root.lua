-- regress_360_multi_nil_allocation_root: 并行 nil overwrite 必须终止每个已逃逸 allocation 的物理 root

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
    end
    return nil, nil, check()
end

local first, second, alive = run()
assert(first == nil and second == nil and not alive)
