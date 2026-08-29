-- regress_416_expired_copy_root: a copy above the restored stack top must expire with its block

local weak_values = setmetatable({}, { __mode = "v" })

local function make()
    local value = {}
    weak_values.value = value
    return value
end

local original = make()

local function callback()
    original = nil
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak_values.value == nil, "expired copy root retained")
end

local function run()
    do
        local padding = 1
        local dead_copy = original
    end
    callback()
end

collectgarbage("stop")
run()
print("regress_416_expired_copy_root", "OK")
