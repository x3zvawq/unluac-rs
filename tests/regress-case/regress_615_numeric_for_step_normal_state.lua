-- 正常后继的step残根：54/55 skip可保留字符串，51–53先数值化；一次迭代后均释放。
local seen = {}
local baseline = 0
local old = getmetatable(_G)
setmetatable(_G, {__index = function(_, key)
    if key == "normal_state_step" then
        return string.rep("0", 1048576) .. "1"
    elseif key == "normal_state_observe" then
        collectgarbage("collect")
        seen[#seen + 1] = tostring(collectgarbage("count") - baseline > 512)
        return 0
    end
end})
local function check(limit)
    for index = 2, limit, normal_state_step do end
    return normal_state_observe
end
collectgarbage("collect")
baseline = collectgarbage("count")
check(1)
collectgarbage("collect")
baseline = collectgarbage("count")
check(2)
setmetatable(_G, old)
print("normal-state-step", table.concat(seen, ","))
local expected = (_VERSION == "Lua 5.4" or _VERSION == "Lua 5.5") and "true,false" or "false,false"
assert(table.concat(seen, ",") == expected)
