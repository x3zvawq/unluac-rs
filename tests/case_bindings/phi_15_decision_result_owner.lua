-- 完整值决策保留原 phi 结果，条件重赋值不能引入额外身份并抬高后继调用前缀。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[local-binding]] [[21]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
local function exercise(flag, replace)
    local function run() print("old") end
    if flag then run = replace(run) end
    run()
    local function store(owner, selected)
        owner.selected = selected
    end
    for scenario = 1, 3 do
        local owner = {}
        store(owner, scenario ~= 1)
        assert(owner.selected == (scenario ~= 1))
    end
end
local calls = 0
local function replace(original)
    calls = calls + 1
    original()
    return function() print("new") end
end
exercise(false, replace)
assert(calls == 0)
exercise(true, replace)
assert(calls == 1)
exercise(false, replace)
assert(calls == 1)
print("decision-result-owner", calls)

-- 捕获体使调用准备 COPY 先提升为 Local；仍须先写回原决策结果，再复制到 callee。
local function exercise_captured(flag, replace_captured)
    local trace = ""
    local function run(value) trace = trace .. value end
    if flag then run = replace_captured(run) end
    run("!")
    local function store(owner, selected)
        owner.selected = selected
    end
    for scenario = 1, 3 do
        local owner = {}
        store(owner, scenario ~= 1)
        assert(owner.selected == (scenario ~= 1))
    end
    return trace
end
calls = 0
local function replace_captured(original)
    calls = calls + 1
    original("prepare")
    return function(value) original("new" .. value) end
end
assert(exercise_captured(false, replace_captured) == "!" and calls == 0)
assert(exercise_captured(true, replace_captured) == "preparenew!" and calls == 1)
assert(exercise_captured(false, replace_captured) == "!" and calls == 1)
print("captured-decision-owner", calls)

-- 包含决策 callee 的调用只抽取其前缀，返回值声明应留在实际调用之后。
local function exercise_result(flag, replace_result)
    local function run() return "old" end
    if flag then run = replace_result(run) end
    local result = run()
    local function store(owner, selected)
        owner.selected = selected
    end
    for scenario = 1, 3 do
        local owner = {}
        store(owner, scenario ~= 1)
        assert(owner.selected == (scenario ~= 1))
    end
    return result
end
calls = 0
local function replace_result(original)
    assert(original() == "old")
    calls = calls + 1
    return function() return "new" end
end
assert(exercise_result(false, replace_result) == "old" and calls == 0)
assert(exercise_result(true, replace_result) == "new" and calls == 1)
assert(exercise_result(false, replace_result) == "old" and calls == 1)
print("decision-return-declaration", calls)
