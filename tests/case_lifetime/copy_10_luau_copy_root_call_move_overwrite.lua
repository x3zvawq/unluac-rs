-- regress_458_luau_copy_root_call_move_overwrite: unread copy root survives a call until its result MOVE overwrites the old home
-- unluac: expect-not-contains [[unluac error]]

local weak_values = setmetatable({}, { __mode = "v" })

local function make()
    local value = {}
    weak_values[1] = value
    return value
end

local original = make()

local function observe_prior()
    assert(weak_values[1] ~= nil)
end

local function replacement()
    original = nil
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak_values[1] ~= nil, "copy root was lost before call-result MOVE")
    return "replacement"
end

local function run()
    local padding = 1
    local root_copy = original
    observe_prior()
    root_copy = replacement()
    assert(root_copy == "replacement")
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak_values[1] == nil, "copy root survived after call-result MOVE")
end

collectgarbage("collect")
run()
print("regress_458_luau_copy_root_call_move_overwrite", "OK")
