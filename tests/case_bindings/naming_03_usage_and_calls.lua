-- 相同用途可以聚合，冲突用途不选第一次遍历的字段；捕获与遮蔽仍按 binding 身份处理。
-- unluac: expect-contains [[local lvl =]] [[@naming-mode=heuristic]]
-- unluac: expect-contains [[local value =]] [[@naming-mode=heuristic]]
-- unluac: expect-contains [[local slot =]] [[@naming-mode=heuristic]]
-- unluac: expect-contains [[local slot2 =]] [[@naming-mode=heuristic]]
-- unluac: expect-contains [[local user =]] [[@naming-mode=heuristic]]
-- unluac: expect-contains [[(_, _)]] [[@naming-mode=heuristic]]
-- unluac: expect-contains [[local print2 =]] [[@naming-mode=heuristic]]
-- unluac: expect-contains [[local config =]] [[@naming-mode=heuristic]]
-- unluac: expect-contains [[local result2 = getaway()]] [[@naming-mode=heuristic]]
-- unluac: expect-contains [[local items =]] [[@naming-mode=heuristic]]
-- unluac: expect-name [[param:0]] [[a]] [[@proto=5]] [[@dialect=lua5.4]] [[@naming-mode=heuristic]]
-- unluac: expect-name [[param:1]] [[_]] [[@proto=5]] [[@dialect=lua5.4]] [[@naming-mode=heuristic]]
-- unluac: expect-name [[upvalue:0]] [[a]] [[@proto=6]] [[@dialect=lua5.4]] [[@naming-mode=heuristic]]
local old_require = require
require = function(path) return { path = path } end
local cfg = require("app.data.cfg.slot")
local other = require("app.ui.slot")
print(cfg.path, other.path)
require = old_require
function getUser()
    return { id = 17 }
end
local person = getUser()
print(person.id)
function naming_usage(input, ambiguous)
    local first = input + 1
    local second = ambiguous + 0
    local record = {}
    record.lvl = first
    record.left = second
    record.right = second
    print(first, second, record.lvl, record.left, record.right)
    return record
end
local record = naming_usage(6, 9)
assert(record.lvl == 7 and record.left == 9 and record.right == 9)
function naming_unused(a, b)
    return 42
end
function naming_capture(first, second)
    return function() return first end
end
assert(naming_unused(1, 2) == 42)
assert(naming_capture(31, 32)() == 31)

-- 用途提示不能遮蔽真实全局；词边界外的 getaway 也不是 get + away。
function naming_conflict(input)
    local value = input + 1
    local out = { print = value }
    print(value, out.print)
    return out.print
end
function read_config() return { enabled = true } end
function getaway() return 19 end
local settings = read_config()
local unknown = getaway()
print(settings.enabled, unknown)
assert(settings.enabled and unknown == 19 and naming_conflict(5) == 6)
local methods = { getItems = function() return { 4, 5 } end }
local entries = methods:getItems()
print(entries[1], entries[2])
assert(entries[1] + entries[2] == 9)
