-- regress_314_lvalue_key_deferred_base: append key 与 inherited upvalue base 的方言顺序
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- 计算目标直接消费原单结果 CALL；低槽键保留其较早求值，不生成 callee/结果接棒变量。
-- unluac: expect-ast-count [[local-binding]] [[20]] [[@proto=0]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=14]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=14]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=14]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=14]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=14]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=14]] [[@dialect=luau]]
-- 动态键的 CALL 与低槽 index 共用原算术准备，不保留额外目标或 CALL 结果声明。
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=13]] [[@dialect=luau]]
local proxy_factory = rawget(_G, "newproxy")

local function observed_table(on_length, on_write)
    if proxy_factory then
        local value = proxy_factory(true)
        local metatable = getmetatable(value)
        metatable.__len = on_length
        metatable.__newindex = on_write
        return value
    end
    return setmetatable({}, {
        __len = on_length,
        __newindex = on_write,
    })
end

-- #1: PUC Lua 5.2-5.5 可在 key 后读取 upvalue；其它方言必须保留快照
local subject
local replacement
local old_writes = 0
local new_writes = 0

local function length_and_replace()
    subject = replacement
    return 0
end

local original = observed_table(length_and_replace, function()
    old_writes = old_writes + 1
end)
replacement = observed_table(function()
    return 0
end, function()
    new_writes = new_writes + 1
end)
subject = original

local function write_after_length()
    local index = #subject + 1
    subject[index] = "value"
end

write_after_length()
assert(old_writes == 0)
assert(new_writes == 1)
print("regress_314_lvalue_key_deferred_base#1", "OK")

-- #2: complex base 必须保留在 append key producer 之后
local complex_order = {}
local complex_writes = 0
local complex_target = observed_table(function()
    complex_order[#complex_order + 1] = "key"
    return 0
end, function()
    complex_writes = complex_writes + 1
end)
local function pick_target()
    complex_order[#complex_order + 1] = "base"
    return complex_target, "discarded"
end
local complex_index = #complex_target + 1
pick_target()[complex_index] = "value"
assert(table.concat(complex_order, ",") == "key,base")
assert(complex_writes == 1)
print("regress_314_lvalue_key_deferred_base#2", "OK")

-- #3: key 内更早的可观察前缀仍阻断 append producer 搬运
local prefix_log = {}
local prefix_writes = 0
local prefix_target = observed_table(function()
    prefix_log[#prefix_log + 1] = "producer"
    return 0
end, function()
    prefix_writes = prefix_writes + 1
end)
local function mark_prefix()
    prefix_log[#prefix_log + 1] = "prefix"
    return 0
end
local function write_after_prefix()
    local index = #prefix_target + 1
    prefix_target[mark_prefix() + index] = "value"
end
write_after_prefix()
assert(table.concat(prefix_log, ",") == "producer,prefix")
assert(prefix_writes == 1)
print("regress_314_lvalue_key_deferred_base#3", "OK")

-- 参数 callee 与现成的低槽 key 也使用同一目标准备协议，CALL 只取一个结果。
local function write_call_target(factory, index)
    factory()[index] = "value"
end
write_call_target(pick_target, 2)
assert(complex_writes == 2)
assert(table.concat(complex_order, ",") == "key,base,base")
print("call target", complex_writes)
