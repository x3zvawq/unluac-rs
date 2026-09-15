-- Boolean 值的原槽覆盖不能退化成谓词极性；不同 VM 的存活结果由各自源码基线决定。
-- 后续 callee 的 __index 在赋入目标槽之前观察 GC，调用前插入的临时槽也会影响结果。
local weak = setmetatable({}, {__mode="v"})
local function probe()
    local value = {}
    weak.value = value
    return value
end
local methods = setmetatable({}, {__index=function()
    collectgarbage("collect")
    collectgarbage("collect")
    local observed = weak.value ~= nil
    return function() return observed end
end})

local function double_value(a,b)
    return a and not not probe() and b or methods.next()
end

local function double_local()
    local flag = not not probe()
    if flag then return methods.next() else return true end
end

-- 这里的条件没有原 Boolean 值写回，不能为了恢复 and/or 添加双 not。
local function predicate(a,b)
    if a and probe() and b then
        return b
    else
        return methods.next()
    end
end

-- 单 not 出口不意味着所有 VM 都在后续查找前丢弃原调用结果。
local function single_value(a)
    return a and not probe() or methods.next()
end

local function single_local()
    local flag = not probe()
    if flag then return true else return methods.next() end
end

-- 独立源码 local 的原根与 Boolean 临时值是不同的生命周期事实。
local function retained_value(a)
    local saved = probe()
    return a and not saved or methods.next()
end

local function logical_value(b)
    local flag = not not probe()
    return flag and b or methods.next()
end

local function copied_value(b)
    local flag = not not probe()
    local alias = flag
    if alias then return methods.next() else return true end
end

local function compared_value(b)
    local flag = not not probe()
    if flag == true then return methods.next() else return true end
end

print("double_value", double_value(true,false))
print("double_local", double_local())
print("predicate", predicate(true,false))
print("single_value", single_value(true))
print("single_local", single_local())
print("retained_value", retained_value(true))
print("logical_value", logical_value(false))
print("copied_value", copied_value(false))
print("compared_value", compared_value(false))
