-- 最终写回原 home 不代表中间 GETTABLE 也覆盖它；元方法在外层查找时观察旧根。
-- 存活结果按各 VM 的源码基线比较，显式 local 与直接表达式分别保持原窗口。
local function overwrite(holder)
    local root = holder.value
    root = root.child.result
    return root
end

local function expression(holder)
    return holder.value.child.result
end

local function dynamic_key(holder, key)
    local root = holder.value
    root = root[key()].result
    return root
end

local function run(label, read)
    collectgarbage("stop")
    local weak = setmetatable({}, {__mode = "v"})
    local proxy = setmetatable({}, {__index = function()
        collectgarbage("collect")
        collectgarbage("collect")
        print(label, "result", weak.value ~= nil)
        return 17
    end})
    local holder = setmetatable({}, {__index = function()
        local value = setmetatable({}, {__index = function() return proxy end})
        weak.value = value
        return value
    end})
    local function key()
        collectgarbage("collect")
        collectgarbage("collect")
        print(label, "key", weak.value ~= nil)
        return "child"
    end
    assert(read(holder, key) == 17)
    collectgarbage("restart")
end

run("overwrite", overwrite)
run("expression", expression)
run("dynamic", dynamic_key)
