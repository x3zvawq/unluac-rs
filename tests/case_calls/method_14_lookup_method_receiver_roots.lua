-- SELF 的 callee 覆盖结束低槽 lookup 根，首参仍须活过 method lookup 与参数求值。
-- 显式 local receiver 有独立低槽；各 VM 的根存活由各自源码执行基线比较。
local weak = setmetatable({}, {__mode = "v"})
local label
local function observe(where)
    collectgarbage("collect")
    collectgarbage("collect")
    print(label, where, weak.value ~= nil)
    return 17
end
local methods = setmetatable({}, {__index = function()
    observe("lookup")
    return function(self, value)
        assert(value == 17)
        self = nil
        observe("call")
    end
end})
local provider = setmetatable({}, {__index = function()
    local value = setmetatable({}, {__index = methods})
    weak.value = value
    return value
end})

local function direct()
    provider.worker:touch(observe("argument"), 0)
    observe("after")
end
local function retained()
    local receiver = provider.worker
    receiver:touch(observe("argument"), 0)
    observe("after")
end

collectgarbage("stop")
label = "direct"
direct()
label = "retained"
retained()
collectgarbage("restart")

-- 全局字段写在高槽读取目标，之前的低槽方法结果已经是独立 local。
-- receiver 准备若残留为声明，会同时阻断后继嵌套数组的原 SETLIST 帧。
-- unluac: expect-contains [[ui.BasePopup:inherit()]]
-- unluac: expect-ast-count [[table-list-field]] [[6]]
-- unluac: expect-contains [[ui.ChallengeScreen = ui.BasePopup:inherit()]]
do
    local old_ui, old_load, old_path = ui, loadLuaFile, scriptPath
    local trace = ""
    local base = {}
    function base:inherit()
        assert(self == base)
        trace = trace .. "inherit;"
        return {}
    end
    ui = { BasePopup = base }
    scriptPath = "root"
    loadLuaFile = function(path, label, first, second)
        assert(ui.ChallengeScreen ~= nil and label == "" and not first and not second)
        trace = trace .. path .. ";"
    end
    local function install()
        local class = ui.BasePopup:inherit()
        ui.ChallengeScreen = class
        loadLuaFile(scriptPath .. "/one", "", false, false)
        loadLuaFile(scriptPath .. "/two", "", false, false)
        local count, enabled = 5, false
        local entries = { { a = 1, b = 2 }, { a = 3, b = 4 }, { a = 5, b = 6 } }
        function class.run() return count, enabled, entries end
    end
    install()
    local count, enabled, entries = ui.ChallengeScreen.run()
    assert(count == 5 and enabled == false and #entries == 3)
    assert(entries[1].a == 1 and entries[2].b == 4 and entries[3].b == 6)
    assert(trace == "inherit;root/one;root/two;")
    print("method result before global field", trace, count, enabled, entries[3].b)
    -- 此处目标表快照先于 RHS 的方法调用，且没有结果 local 可作为边界。
    local function install_direct()
        ui.ChallengeScreen = ui.BasePopup:inherit()
        ui.ChallengeScreen.showInEditor = true
        local entries = { { a = 1, b = 2 }, { a = 3, b = 4 }, { a = 5, b = 6 } }
        ui.ChallengeScreen.entries = entries
    end
    install_direct()
    assert(ui.ChallengeScreen.showInEditor and #ui.ChallengeScreen.entries == 3)
    assert(ui.ChallengeScreen.entries[2].a == 3 and ui.ChallengeScreen.entries[3].b == 6)
    assert(trace == "inherit;root/one;root/two;inherit;")
    print("method result in global field", trace, ui.ChallengeScreen.entries[3].b)
    ui, loadLuaFile, scriptPath = old_ui, old_load, old_path
end
