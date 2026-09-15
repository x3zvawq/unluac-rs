-- 覆写后的两条纯分支可共享 frame 出口；分支内的观察仍须结束旧对象的根。
-- unluac: expect-ast-min [[if]] [[1]]
local gc = collectgarbage
local weak = setmetatable({}, {__mode = "v"})
local function make()
    local value = {}
    weak[1] = value
    return value
end
local function observe()
    local found = false
    for index = 1, 40 do
        local name = debug.getlocal(2, index)
        if not name then break end
        if name == "owner" then
            debug.setlocal(2, index, nil)
            found = true
            break
        end
    end
    assert(found, "owner parameter missing")
    gc("collect")
    assert(weak[1] ~= nil, "copy released before overwrite")
end
local function joined_exit(owner, flag, callback)
    local copy = owner
    callback()
    copy = owner
    if flag then flag = false else flag = true end
    return flag
end
local function observed_exit(owner, flag, callback)
    local copy = owner
    callback()
    copy = owner
    if flag then flag = false else flag = true end
    gc("collect")
    assert(weak[1] == nil, "copy retained across observing suffix")
    return flag
end
for _, flag in ipairs({false, true}) do
    assert(joined_exit(make(), flag, observe) == not flag, "joined result changed")
    gc("collect")
    assert(weak[1] == nil, "copy survived frame exit")
    assert(observed_exit(make(), flag, observe) == not flag, "observed result changed")
end
print("regress_544_copy_root_forward_exit", "OK")
