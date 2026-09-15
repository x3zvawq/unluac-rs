-- regress_402_method_alias_nested_write_ids: child direct writes do not target an outer same-numbered alias
-- 点调用的参数 COPY 在 lookup 后发生；SELF 预写会提前清掉旧参数槽中的根。
-- unluac: expect-contains [[r1_0.m(r1_0)]]
-- unluac: expect-ast-count [[method-call]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]

local function run(obj)
    local receiver = obj
    receiver.m(receiver)

    local function later(flag, side, other, use)
        local receiver
        if flag then
            receiver = side()
        else
            receiver = other()
        end
        use(receiver)
        return receiver
    end

    return later
end

local calls = 0
local receiver = {
    m = function(self)
        calls = calls + 1
        assert(self.tag == "receiver")
    end,
    tag = "receiver",
}
local later = run(receiver)
local left, right = {}, {}
local seen = {}
local function record(value)
    seen[#seen + 1] = value
end
assert(later(true, function() return left end, function() return right end, record) == left)
assert(later(false, function() return left end, function() return right end, record) == right)
assert(calls == 1 and seen[1] == left and seen[2] == right)

-- 非 vararg 函数仍可能收到额外实参。第四个实参占据尚未 COPY 的 receiver 参数槽；
-- __index 期间原点调用保留它，SELF 则已把该槽改写为 receiver。无需数字槽位反射。
local lookup_weak = setmetatable({}, {__mode = "v"})
local lookup_calls, dispatched_calls = 0, 0
local lookup_receiver = setmetatable({tag = "old"}, {
    __index = function(_, key)
        assert(key == "m")
        lookup_calls = lookup_calls + 1
        collectgarbage("collect")
        collectgarbage("collect")
        assert(lookup_weak[1] ~= nil, "method lookup lost its incoming argument root")
        return function(self)
            dispatched_calls = dispatched_calls + 1
            assert(self.tag == "old")
        end
    end,
})
local function fresh_lookup_root()
    local value = {}
    lookup_weak[1] = value
    return value
end
collectgarbage("stop")
local returned = run(lookup_receiver, nil, nil, fresh_lookup_root())
collectgarbage("restart")
assert(type(returned) == "function" and lookup_calls == 1 and dispatched_calls == 1)

-- 返回表字段事实只在尚未被写入/观察的窗口内有效，不能沿返回值永久缓存。
-- unluac: expect-not-contains [[:mutable_field(]]
local published_fields
local function fresh_fields()
    local object = {mutable_field = function(self) return 101 end}
    published_fields = object
    return object
end
local function change_fields(object)
    object.mutable_field = function(self) return "changed" end
    return false
end
local function after_write()
    local object = fresh_fields()
    object.mutable_field = function(self) return "written" end
    return object.mutable_field(object)
end
local function after_call()
    local object = fresh_fields()
    change_fields(object)
    return object.mutable_field(object)
end
local function after_pack()
    local object = fresh_fields()
    local copy, unused = object, change_fields(object)
    return copy.mutable_field(copy), unused
end
local function return_pack()
    local object = fresh_fields()
    return object, change_fields(object)
end
local function after_return_pack()
    local object = return_pack()
    return object.mutable_field(object)
end
local field_sink = setmetatable({}, {__newindex = function()
    change_fields(published_fields)
end})
local function after_store()
    local object
    object, field_sink.value = fresh_fields(), false
    return object.mutable_field(object)
end
local function cleanup_fields()
    local object = fresh_fields()
    local closer <close> = setmetatable({}, {__close = function()
        change_fields(object)
    end})
    return object
end
local function after_cleanup()
    local object = cleanup_fields()
    return object.mutable_field(object)
end
assert(after_write() == "written")
assert(after_call() == "changed")
local pack_value, pack_unused = after_pack()
assert(pack_value == "changed" and pack_unused == false)
assert(after_return_pack() == "changed")
assert(after_store() == "changed")
assert(after_cleanup() == "changed")
