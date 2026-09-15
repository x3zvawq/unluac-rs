-- A dynamic callable producer must keep its local root across a non-tail call.
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=6]] [[@dialect=lua5.4]]

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

-- A sibling can replace a captured factory after its direct-closure initialization.
-- Its original return type must not authorize removing the terminal callable's root.
local terminal_factory = function()
    return function() observed = false end
end
local function run_terminal_factory()
    local callable = terminal_factory()
    callable()
end
local function replace_terminal_factory()
    terminal_factory = make_callable
end
replace_terminal_factory()
observed = false
collectgarbage("stop")
run_terminal_factory()
collectgarbage("restart")
assert(observed == true)
print("regress_460_non_tail_callable_root", "OK")
