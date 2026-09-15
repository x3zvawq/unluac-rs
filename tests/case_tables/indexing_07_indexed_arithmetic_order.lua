-- 元方法改变低槽 key 和原 target 来源：写表仍使用原目标快照、最终 key 读取。
local function run()
    local log = {}
    local key = "before"
    local original = {}
    local replacement = {}
    local selected = original
    local source = setmetatable({}, {__index = function(_, field)
        log[#log + 1] = "target:" .. field
        return selected
    end})
    local value = setmetatable({}, {__add = function()
        key = "after"
        selected = replacement
        log[#log + 1] = "add"
        return 21
    end})
    local input = setmetatable({}, {__index = function(_, field)
        log[#log + 1] = "rhs:" .. field
        return value
    end})
    source.branch[key] = input.value + 1
    assert(original.after == 21 and original.before == nil)
    assert(next(replacement) == nil)
    print("order", table.concat(log, ","), original.after)
end
run()

local function roots()
    local weak = setmetatable({}, {__mode = "v"})
    local root = setmetatable({}, {__index = function(_, field)
        if field == "first" then
            local branch = setmetatable({}, {__index = function() return 4 end})
            weak.branch = branch
            return branch
        end
        collectgarbage("collect")
        collectgarbage("collect")
        print("lookup-root", weak.branch ~= nil)
        return {value = 5}
    end})
    local target = {}
    collectgarbage("stop")
    target[1] = root.first.value + root.second.value
    assert(target[1] == 9)
    collectgarbage("restart")
end
roots()
