-- 参数的匿名并行赋值快照必须活过查找回调，在查找写回后立即退休。
-- unluac: expect-contains [[owner, iteration = owner, 0]]
-- unluac: expect-contains [[snapshot_missing()]]
-- unluac: expect-ast-max [[local-binding]] [[11]]
-- unluac: expect-ast-count [[function]] [[4]]
local gc = collectgarbage
local weak = setmetatable({}, {__mode = "v"})
local phase = 0
local function replacement()
    assert(phase == 1)
    gc("collect")
    assert(weak[1] == nil, "snapshot survived lookup overwrite")
    phase = 2
    print("after-overwrite", "dead")
end
local function run(owner)
    local iteration
    owner, iteration = owner, 0
    snapshot_missing()
    assert(iteration == 0, "iteration changed")
end
setmetatable(_G, {__index = function(_, key)
    assert(phase == 0)
    assert(key == "snapshot_missing", "unexpected lookup")
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
    assert(weak[1] ~= nil, "snapshot released during lookup")
    phase = 1
    print("during-lookup", "alive")
    return replacement
end})
local function make()
    local value = {}
    weak[1] = value
    return value
end
run(make())
setmetatable(_G, nil)
assert(phase == 2)
print("regress_542_observing_snapshot_overwrite", "OK")
