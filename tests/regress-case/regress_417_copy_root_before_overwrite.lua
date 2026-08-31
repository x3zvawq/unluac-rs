-- regress_417_copy_root_before_overwrite: copy root remains live until its explicit nil overwrite

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
    assert(weak_values.value ~= nil, "copy root lost before explicit overwrite")
end

local function run()
    local root_copy = original
    callback()
    root_copy = nil
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak_values.value == nil, "copy root retained after explicit overwrite")
end

collectgarbage("stop")
run()
print("regress_417_copy_root_before_overwrite", "OK")
