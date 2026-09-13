-- 参数COPY跨可观察查找保留独立根，纯nil终点仍须消费原覆盖证书。
local weak = setmetatable({}, {__mode = "v"})
local seen
local old = getmetatable(_G)
setmetatable(_G, {__index = function(_, key)
    if key == "snapshot_observe" then
        debug.setlocal(2, 1, nil)
        collectgarbage("collect")
        seen = weak[1] ~= nil
        return 3
    end
end})
local function probe(object)
    local holder = nil
    holder = object
    weak[1] = holder
    local result = snapshot_observe
    holder = nil
    return result
end
assert(probe({}) == 3)
setmetatable(_G, old)
print("parameter-snapshot-pure-end", seen)
assert(seen)
