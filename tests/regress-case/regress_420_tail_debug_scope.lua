-- regress_420_tail_debug_scope: accepted debug intervals that end before Return/outer close stay nested

local forbidden_name = nil
local armed = false

local function return_hook(event)
    if armed and event == "return" then
        for index = 1, 64 do
            local name = debug.getlocal(2, index)
            assert(name ~= forbidden_name, "tail debug local survived return: " .. forbidden_name)
        end
    end
end

local function plain_tail_scope()
    do
        local inner = 42
        assert(inner == 42)
    end
end

local function close_tail_scope()
    do
        local resource <close> = setmetatable({}, {
            __close = function()
            end,
        })
        assert(resource)
    end
end

local function outer_close_scope()
    local closer <close> = setmetatable({}, {
        __close = function()
            for index = 1, 64 do
                local name = debug.getlocal(2, index)
                assert(name ~= "inner", "tail debug local survived outer close")
            end
        end,
    })

    do
        local inner = 42
        assert(inner == 42)
    end
end

debug.sethook(return_hook, "r")
forbidden_name = "inner"
armed = true
plain_tail_scope()
armed = false
forbidden_name = "resource"
armed = true
close_tail_scope()
armed = false
debug.sethook()

outer_close_scope()
print("regress_420_tail_debug_scope", "OK")
