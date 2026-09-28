-- regress_38_method_chain_live_receiver#1: method-chain sugar 不能删掉后续仍活跃的 receiver local
-- unluac: expect-not-contains [[end)(]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[getLayoutPosition()]]

local function make_child(name)
    return {
        name = name,
        visible = false,
        w = 5,
        x = 0,
        y = 0,
        setVisible = function(self, value)
            self.visible = value
        end,
        getLayoutPosition = function(self)
            return 10, 20
        end,
        setPosition = function(self, x, y)
            self.x = x
            self.y = y
        end,
    }
end

local function sample(root)
    local button = root:getChild("button")
    button:setVisible(true)
    local x, y = button:getLayoutPosition()
    local target_x = x + button.w
    local done = function()
        return button.x
    end
    button:setPosition(target_x, y)
    return button.visible, done(), button.y
end

local root = {
    getChild = function(self, name)
        return make_child(name)
    end,
}

local visible, x, y = sample(root)
assert(visible == true and x == 15 and y == 20)
print("regress_38_method_chain_live_receiver#1", visible, x, y)

-- 带构造器参数的 CALL 结果继续参与 SELF 链，不能提前冻结成独立声明。
-- unluac: expect-contains [[:runWhile(function]]
-- unluac: expect-contains [[:wait(1):runQueues({]]
local function schedule(self, flag)
    local a, b, c, d
    self.queue:run(function() a = self end)
        :runTween({ start = 0, change = 1, duration = 1, callback = function(x) a = x end })
        :run(function() b = a end)
        :runWhile(function() return b end)
        :run(function() c = b end)
        :runTween({ start = 0, change = 2, duration = 1, callback = function(x) c = x end })
        :run(function() d = c end)
        :runTween({ start = 0, change = 3, duration = 1, callback = function(x) d = x end })
    if flag then
        self.queue:run(function() a = nil end)
    else
        self.events:notify({ id = "unlock", step = 60 })
        self.unlocking = true
        self.queue:wait(1):runQueues({ self:unlock() })
    end
    return function() return a, b, c, d end
end

local function check_schedule(flag)
    local pending, trace, lookups = {}, "", ""
    local methods = {}
    local serial = 0
    local function node()
        serial = serial + 1
        local id = serial
        local result
        result = setmetatable({}, { __index = function(_, key)
            lookups = lookups .. id .. ":" .. key .. ";"
            return function(receiver, arg)
                assert(receiver == result, "method receiver changed")
                trace = trace .. key .. ";"
                methods[key](arg)
                return node()
            end
        end })
        return result
    end
    methods.run = function(callback) pending[#pending + 1] = callback end
    methods.runWhile = function(callback)
        pending[#pending + 1] = function() assert(callback() == 11) end
    end
    methods.runTween = function(spec)
        assert(spec.start == 0 and spec.duration == 1)
        pending[#pending + 1] = function() spec.callback(spec.change * 11) end
    end
    methods.wait = function(delay) assert(delay == 1) end
    methods.runQueues = function(queues)
        assert(queues[1] == "first" and queues[2] == nil and queues[3] == "third" and queues[4] == nil)
    end
    local owner = {
        queue = node(),
        events = { notify = function(_, spec)
            assert(spec.id == "unlock" and spec.step == 60)
            trace = trace .. "notify;"
        end },
        unlock = function() trace = trace .. "unlock;"; return "first", nil, "third" end,
    }
    local read = schedule(owner, flag)
    assert(read() == nil)
    assert(#pending == (flag and 9 or 8))
    for _, callback in ipairs(pending) do callback() end
    local a, b, c, d = read()
    assert(a == (not flag and 11 or nil) and b == 11 and c == 22 and d == 33)
    assert(owner.unlocking == (not flag or nil))
    assert(trace == "run;runTween;run;runWhile;run;runTween;run;runTween;" ..
        (flag and "run;" or "notify;wait;unlock;runQueues;"))
    print("constructor method chain", flag, trace, lookups)
end
check_schedule(false)
check_schedule(true)
-- SELF 的 receiver/lookup 在比较参数之前执行；参数分支不能丢掉原方法协议。
-- unluac: expect-contains [[:setPredicate(]]
-- unluac: expect-contains [[== true]]
local function use_predicate_method(owner, flag)
    owner:setPredicate(flag == true)
    local running = owner:current()
    if flag and running == nil then
        local first = owner:newChild({ id = "first" })
        local second = owner:newChild({ id = "second" })
        owner:consume({ first, second })
    end
end
local function check_predicate_method(flag, running)
    local trace, children = "", {}
    local methods = {
        setPredicate = function(_, value)
            assert(value == (flag == true))
            trace = trace .. "predicate;"
        end,
        current = function() trace = trace .. "current;"; return running end,
        newChild = function(_, spec)
            trace = trace .. spec.id .. ";"
            children[#children + 1] = spec
            return spec, "discarded"
        end,
        consume = function(_, values)
            assert(values[1] == children[1] and values[2] == children[2] and values[3] == nil)
            trace = trace .. "consume;"
        end,
    }
    local owner = setmetatable({}, { __index = function(_, key)
        trace = trace .. "get:" .. key .. ";"
        return methods[key]
    end })
    use_predicate_method(owner, flag)
    assert(trace == "get:setPredicate;predicate;get:current;current;" ..
        ((flag and running == nil) and "get:newChild;first;get:newChild;second;get:consume;consume;" or ""))
    print("method predicate prefix", flag == true, running == nil, trace)
end
check_predicate_method(true, nil)
check_predicate_method(false, nil)
check_predicate_method(nil, nil)
check_predicate_method({}, nil)
check_predicate_method(true, false)
