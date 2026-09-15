-- 原生表初始化尚未暴露 source binding；初始化后的回调能通过该身份安装元表。
local getlocal = debug.getlocal
local source = setmetatable({}, {
    __index = function(_, key)
        for index = 1, 32 do
            local name = getlocal(2, index)
            if not name then break end
            assert(name ~= "ids", "initializer exposed source binding early")
        end
        if key == "last" then return "last" end
    end,
})
local function build()
    local ids = { source.first, source.middle, source.last }
    return ids[1], ids[2], ids[3]
end
local first, middle, last = build()
assert(first == nil and middle == nil and last == "last")

local function patch()
    for index = 1, 32 do
        local name, value = getlocal(2, index)
        if not name then break end
        if name == "visible" then
            setmetatable(value, { __index = function() return "patched" end })
            return
        end
    end
    error("source binding missing")
end
local function after_initializer()
    local visible = {}
    patch()
    return visible[1]
end
assert(after_initializer() == "patched", "visible table incorrectly treated as plain")
print("regress_539_initializer_plain_table_scope", first, middle, last, "patched")
