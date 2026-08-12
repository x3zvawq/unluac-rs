-- regress_314_lvalue_key_deferred_base: append key 与 inherited upvalue base 的方言顺序
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
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
    return complex_target
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
