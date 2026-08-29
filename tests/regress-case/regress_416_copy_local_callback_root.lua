-- regress_416_copy_local_callback_root: an unread copy local remains a strong root through callback execution

local weak_values = setmetatable({}, { __mode = "v" })

local function make()
    local value = {}
    weak_values.value = value
    return value
end

local original = make()
local object = {}

function object:first()
    return self
end

function object:invoke(callback)
    callback()
end

local function run()
    local root_copy = original
    local chain = object:first()
    chain:invoke(function()
        original = nil
        collectgarbage("collect")
        collectgarbage("collect")
        assert(weak_values.value ~= nil, "copy root lost during callback")
    end)
end

collectgarbage("stop")
run()
print("regress_416_copy_local_callback_root", "OK")
