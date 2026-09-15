-- unluac: expect-contains [[.method(]]
-- unluac: expect-contains [[:method()]]
-- 只读 capture 不授权将 GETTABLE 后的 receiver COPY 提前为 SELF；两类 capture 均须保留原根事件。
-- unluac: expect-contains [[.readonly_each(]]
-- unluac: expect-not-contains [[:writable_each() do]]
-- unluac: expect-not-contains [[function p8_0.field]]

local methods = {}

function methods:readonly_each()
    return ipairs(self.values)
end

function methods:writable_each()
    return ipairs(self.values)
end

local weak_receivers = setmetatable({}, { __mode = "v" })
local next_receiver = 0

local function new_receiver()
    next_receiver = next_receiver + 1
    local receiver = setmetatable({ values = { 10, 20 } }, { __index = methods })
    weak_receivers[next_receiver] = receiver
    return receiver, next_receiver
end

local function collect_readonly(source, weak_index)
    local function observe()
        return source
    end

    local values = {}
    local receiver = source
    for _, value in receiver.readonly_each(receiver) do
        collectgarbage("collect")
        assert(weak_receivers[weak_index] ~= nil)
        values[#values + 1] = value
    end
    assert(observe() == source)
    return table.concat(values, ",")
end

local replacement = { values = { 30, 40 } }

local function collect_writable(source, weak_index)
    local function replace()
        source = replacement
    end

    local values = {}
    local receiver = source
    for _, value in receiver.writable_each(receiver) do
        replace()
        collectgarbage("collect")
        assert(weak_receivers[weak_index] ~= nil, "receiver root was released during the loop")
        values[#values + 1] = value
    end
    assert(source == replacement)
    return table.concat(values, ",")
end

local readonly = collect_readonly(new_receiver())
local writable = collect_writable(new_receiver())
assert(readonly == "10,20", readonly)
assert(writable == "10,20", writable)

local forwarded_replacement = {}
local function install_forwarded(target)
    local function replace()
        target = forwarded_replacement
    end

    local forwarded = function()
        return replace
    end
    target.field = forwarded
    return target
end

local forwarded_target = {}
assert(install_forwarded(forwarded_target) == forwarded_target)
assert(type(forwarded_target.field()) == "function")

print("regress_428_method_alias_capture_writes", readonly, writable)

-- 保留 receiver 声明仍不能把 GETFIELD 后的 MOVE 提前到 __index 之前。
do
    local weak = setmetatable({}, { __mode = "v" })
    local seen = {}
    
    local method = function(self)
        return self
    end
    
    local receiver = setmetatable({}, {
        __index = function(_, key)
            assert(key == "method")
            collectgarbage("collect")
            seen[#seen + 1] = weak[1] ~= nil
            return method
        end,
    })
    
    local function make_receiver_with_scratch()
        local result = receiver
        local resource = {}
        weak[1] = resource
        return result
    end
    
    local function effectful_dot()
        local retained = make_receiver_with_scratch()
        return retained.method(retained)
    end
    
    local function effectful_colon()
        local retained = make_receiver_with_scratch()
        return retained:method()
    end
    
    assert(effectful_dot() == receiver)
    assert(effectful_colon() == receiver)
    print("retained-effectful-scratch", seen[1], seen[2])
    assert(seen[1] == true and seen[2] == false)
end
