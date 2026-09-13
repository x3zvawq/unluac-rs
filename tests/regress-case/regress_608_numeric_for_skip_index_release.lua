-- FORPREP 的零次迭代可以保留原 index 字符串。nil 写必须留在原位置、原槽，
-- 不能因没有表达式读取而消失，也不能在循环前新增保活 holder。
local snapshots = {}
local old = getmetatable(_G)
local baseline = 0
local function make()
    return string.rep("0", 1048576) .. "9.125"
end
setmetatable(_G, {__index = function(_, key)
    if key == "for_skip_observe" then
        collectgarbage("collect")
        -- 比较相对基线而非精确字节数；1 MiB 与 512 KiB 的间距隔离普通分配噪声。
        snapshots[#snapshots + 1] = collectgarbage("count") - baseline > 512
        return 0
    end
end})
local function uncleared()
    for index = make(), 1, 1 do error("entered") end
    local observed = for_skip_observe
    return observed
end
local function cleared()
    for index = make(), 1, 1 do error("entered") end
    local discarded = nil
    local observed = for_skip_observe
    return observed
end
local function prefix()
    local kept = 13
    for index = make(), 1, 1 do error("entered") end
    local discarded = nil
    local observed = for_skip_observe
    return kept, observed
end
local function nested()
    do
        for index = make(), 1, 1 do error("entered") end
        local discarded = nil
        local observed = for_skip_observe
    end
end
local function nonzero()
    for index = make(), 10, 1 do end
    local observed = for_skip_observe
    return observed
end
local function sequential()
    for index = make(), 1, 1 do error("entered") end
    local first = nil
    local observed = for_skip_observe
    for index = make(), 1, 1 do error("entered") end
    local second = nil
    local observed2 = for_skip_observe
    return observed, observed2
end
collectgarbage("collect")
baseline = collectgarbage("count")
uncleared()
cleared()
prefix()
nested()
nonzero()
sequential()
setmetatable(_G, old)
assert(snapshots[1] == true and snapshots[2] == false)
assert(snapshots[4] == false and snapshots[5] == false)
-- prefix/连续循环的其它高槽残值在 5.4/5.5 上不同，由各自原源码运行比较。
for i = 1, #snapshots do print("skip-index", i, snapshots[i]) end
