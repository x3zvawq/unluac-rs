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

-- Boolean 写回也消费完整算术/比较帧；比较元方法先改写低槽 key，
-- SETTABLE 随后读取该 key，并且每次 __newindex 都观察最终 Boolean。
-- unluac: expect-contains [=[target["computed-" .. key] = operand % 2 < right]=] [[@debug=retained]]
local function comparison_writes()
    local trace = ""
    local key = "before"
    local target = setmetatable({}, {__newindex = function(_, field, value)
        trace = trace .. field .. ":" .. tostring(value) .. ";"
    end})
    local meta = {__lt = function()
        key = "after"
        trace = trace .. "compare;"
        return true
    end}
    local left, right = setmetatable({}, meta), setmetatable({}, meta)
    local operand = setmetatable({}, {__mod = function(_, divisor)
        assert(divisor == 2)
        trace = trace .. "mod;"
        return left
    end})
    target[key] = operand % 2 < right
    target.accepted = operand % 2 < right
    target.rejected = not (operand % 2 < right)
    assert(trace == "mod;compare;after:true;mod;compare;accepted:true;mod;compare;rejected:false;")
    trace, key = "", "before"
    target["computed-" .. key] = operand % 2 < right
    assert(trace == "mod;compare;computed-before:true;")
    print("comparison-writes", trace)
end
comparison_writes()
