-- 正常返回值域必须按槽传播；已知callee与未知候选、可变capture不能合并成肯定证明。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[table-set-list]]

local function constants()
    return 11, "second", false
end

local function empty()
end

local function varied(flag)
    if flag then
        return 3, "tail"
    end
    return false
end

local function mixed()
    return 7, { tag = "resource" }
end

local a, b, c, d = constants()
local missing_a, missing_b = empty()
local number, object = mixed()
print("regress_575#slots", a, b, c, d, missing_a, missing_b, number, object.tag)
print("regress_575#width", select("#", constants()), select("#", empty()))
print("regress_575#varied", varied(true))
print("regress_575#varied", varied(false))

local function aliases()
    local callee = constants
    local saved = callee
    callee = function() return "replacement" end
    return saved(), callee()
end
print("regress_575#alias", aliases())

local function unknown_branch(flag, external)
    local callee
    if flag then
        callee = constants
    else
        callee = external
    end
    local result = callee()
    return type(result)
end
local function resource()
    return {}
end
print("regress_575#join", unknown_branch(true, resource), unknown_branch(false, resource))

local function callee_snapshot()
    local function old() return "old" end
    local function new() return "new" end
    local callee = old
    local function rebind()
        callee = new
        return "argument"
    end
    local first = callee(rebind())
    return first, callee()
end
print("regress_575#callee-before-args", callee_snapshot())

local function captured()
    local cell = 1
    local function read() return cell end
    local function change() cell = {} end
    local before = type(read())
    change()
    return before, type(read())
end
print("regress_575#captured", captured())

local function known_local_constructor()
    local function literals() return 5, "six" end
    local alias = literals
    local values = { alias(), "end" }
    return table.concat(values, ",")
end
print("regress_575#known-constructor", known_local_constructor())

local function recursive(count)
    if count == 0 then return "done", 2 end
    return recursive(count - 1)
end
print("regress_575#recursive", recursive(2))

local function second_result_root()
    local function pair() return 1, {} end
    local weak = setmetatable({}, { __mode = "v" })
    local _, value = pair()
    weak.value = value
    local owner = { value }
    value = nil
    collectgarbage("collect")
    print("regress_575#second-held", weak.value ~= nil, owner[1] ~= nil)
    owner[1] = nil
    collectgarbage("collect")
    print("regress_575#second-released", weak.value ~= nil)
end
second_result_root()

-- 比较结果写入另一个原槽时，读取值仍是独立root，不能套用同槽Boolean交接。
local function separate_comparison_home()
    local weak = setmetatable({}, { __mode = "v" })
    local owner = { {} }
    weak.value = owner[1]
    local retained = owner[1]
    local flag = retained ~= nil
    owner[1] = nil
    collectgarbage("collect")
    print("regress_575#different-home", weak.value ~= nil, flag)
    return flag
end
separate_comparison_home()
