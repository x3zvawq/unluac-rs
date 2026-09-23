-- RETURN 自身拥有的 TBC 生命周期复用函数域；在 RETURN 前结束的 debug 内层域仍保留。
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=3]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=5]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=7]]

local forbidden_name = nil
local armed = false
local outer_close_count = 0

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

local function local_function_tail_scope()
    do
        local function inner_function()
            return 42
        end
        assert(inner_function() == 42)
    end
end

local function outer_close_scope()
    local closer <close> = setmetatable({}, {
        __close = function(self)
            outer_close_count = outer_close_count + 1
            local found_closer = false
            for index = 1, 64 do
                local name, value = debug.getlocal(2, index)
                assert(name ~= "inner", "tail debug local survived outer close")
                if name == "closer" then
                    assert(value == self)
                    found_closer = true
                end
            end
            assert(found_closer, "function local disappeared before return cleanup")
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
forbidden_name = "inner_function"
armed = true
local_function_tail_scope()
armed = false
debug.sethook()

outer_close_scope()
assert(outer_close_count == 1)
print("regress_420_tail_debug_scope", "OK")
