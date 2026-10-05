-- 拼接副本跨过条件取值，保持原可观察覆盖前后的对象寿命。
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=2]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=4]] [[@dialect=luajit]]
local gc = collectgarbage
local weak = setmetatable({}, {__mode = "v"})
local phase = 0
-- 本探针中 LuaJIT 在后续查找前已释放副本，PUC 在该查找回调期间仍保活。
local retained_by_concat = rawget(_G, "jit") == nil
local trace = ""
local replacement = {floor = function(value)
    gc("collect")
    assert(phase == 1 and weak[1] == nil, "concat copy survived observing overwrite")
    phase = 2
    return value
end}
local function check(key)
    trace = trace .. key
    local shift = key == "a" and 1 or key == "b" and 2 or 4
    return concat_snapshot_math.floor(8 / shift)
end
local function make()
    local value = setmetatable({}, {__concat = function(left, right)
        assert(left == "" and right == weak[1])
        local found = false
        for index = 1, 20 do
            local name = debug.getlocal(2, index)
            if name == "key" then
                debug.setlocal(2, index, "a")
                found = true
                break
            end
        end
        assert(found, "key parameter missing")
        return "seen"
    end})
    weak[1] = value
    return value
end
setmetatable(_G, {__index = function(_, key)
    assert(key == "concat_snapshot_math" and phase == 0)
    gc("collect")
    assert((weak[1] ~= nil) == retained_by_concat, "concat copy lifetime changed before overwrite")
    phase = 1
    return replacement
end})
assert(check(make()) == 8)
setmetatable(_G, nil)
assert(phase == 2 and trace == "seen")
print("concat choice copy root", phase, trace)
