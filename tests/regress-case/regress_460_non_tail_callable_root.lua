-- A dynamic callable producer must keep its local root across a non-tail call.

local weak = setmetatable({}, { __mode = "v" })
local observed

local function make_callable()
    local callable = {}
    weak.value = callable
    return setmetatable(callable, {
        __call = function()
            collectgarbage("collect")
            collectgarbage("collect")
            observed = weak.value ~= nil
            return 42
        end,
    })
end

local function run()
    collectgarbage("stop")
    local callable = make_callable()
    return "stable", callable()
end

local prefix, value = run()
collectgarbage("restart")
assert(prefix == "stable" and value == 42)
assert(observed == true)
print("regress_460_non_tail_callable_root", "OK")
