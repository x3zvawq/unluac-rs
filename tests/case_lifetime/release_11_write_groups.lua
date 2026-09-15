-- 完整 LOADNIL 的写义务不取决于旧根来自哪个控制路径。
-- 覆盖合并 nil、分支内 nil、limit/step 槽及多个顺序覆盖；GC 残值按各 VM 原运行比较。
local snapshots = {}
local old = getmetatable(_G)
local baseline = 0
local label = ""
local function make()
    return string.rep("0", 1048576) .. "9.125"
end
local function make_one()
    return string.rep("0", 1048576) .. "1"
end
setmetatable(_G, {__index = function(_, key)
    if key == "for_skip_observe" then
        collectgarbage("collect")
        snapshots[#snapshots + 1] = label .. ":" .. tostring(collectgarbage("count") - baseline > 512)
        return 0
    end
end})
local function nonzero()
    for index = make(), 10, 1 do end
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
local function merged()
    for index = make(), 1, 1 do error("entered") end
    local first, second = nil, nil
    local observed = for_skip_observe
    return observed
end
local function branches(flag)
    for index = make(), 1, 1 do error("entered") end
    if flag then
        local discarded = nil
        local observed = for_skip_observe
        return observed
    else
        local discarded = nil
        local observed = for_skip_observe
        return observed
    end
end
local function limit()
    for index = 9, make_one(), 1 do error("entered") end
    local pad = false
    local discarded = nil
    local observed = for_skip_observe
    return pad, observed
end
local function step()
    for index = 9, 1, make_one() do error("entered") end
    local pad, pad2 = false, true
    local discarded = nil
    local observed = for_skip_observe
    return pad, pad2, observed
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
label = "nonzero"; nonzero()
label = "prefix"; prefix()
label = "nested"; nested()
label = "merged"; merged()
label = "branch-true"; branches(true)
label = "branch-false"; branches(false)
label = "limit"; limit()
label = "step"; step()
label = "sequential"; sequential()
setmetatable(_G, old)
assert(snapshots[1] == "nonzero:false")
assert(snapshots[3] == "nested:false")
assert(snapshots[5] == "branch-true:false")
assert(snapshots[7] == "limit:false")
print(table.concat(snapshots, ","))
