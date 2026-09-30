-- regress_399_branch_state_allocation_capture: allocation may run a finalizer that invalidates captured branch state
-- unluac: expect-not-contains [[unluac error]]
-- 原始 victim 的释放需要局部身份，但 callee/table 准备不应多出中转声明。
-- unluac: expect-ast-count [[local-binding]] [[12]]
-- 接收调用结果后仍须保留清空写，不能改成独立调用加无来源的 nil 声明。
-- unluac: expect-ast-count [[assign]] [[4]] [[@proto=3]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=3]]

local function make()
    return "tag", {}, {}
end

local function new_victim(mt)
    return setmetatable({}, mt)
end

local function run(flag)
    local _, current, other = make()
    local selected
    local finalized = false

    collectgarbage("collect")
    collectgarbage("stop")
    local victim = new_victim({
        __gc = function()
            selected = other
            finalized = true
        end,
    })
    victim = nil
    collectgarbage("restart")
    collectgarbage("incremental", 0, 1, 1)

    selected = current
    for _ = 1, 1000000 do
        local allocation = {}
    end
    assert(finalized)

    if flag then
        selected = current
    else
        selected = other
    end
    return selected == current
end

local environment_mt = getmetatable(_ENV)
setmetatable(_ENV, {
    __newindex = function()
        error("a local overwrite must not become a global write")
    end,
})
assert(run(true))
assert(not run(false))
setmetatable(_ENV, environment_mt)
print("regress_399_branch_state_allocation_capture", "OK")
