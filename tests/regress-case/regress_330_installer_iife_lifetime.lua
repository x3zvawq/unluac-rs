-- regress_330_installer_iife_lifetime: 命名安装器不能延长匿名 IIFE closure 的生命周期
-- unluac: expect-not-contains [[(function(]]

local weak_functions = setmetatable({}, { __mode = "k" })

local function remember_caller()
    weak_functions[debug.getinfo(2, "f").func] = true
    return "remembered"
end

;(function(token)
    local remembered = remember_caller()
    local function exported()
        return token, remembered
    end
    installed = exported
end)("alive")

collectgarbage("collect")

local live_functions = 0
for _ in pairs(weak_functions) do
    live_functions = live_functions + 1
end

assert(live_functions == 0)
local value, remembered = installed()
assert(value == "alive" and remembered == "remembered")
print("regress_330_installer_iife_lifetime", live_functions, value, remembered)
