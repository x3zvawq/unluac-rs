-- 用户槽在body可持有对象，最后一次FORLOOP退出不等于再次物理写入该槽。
-- unluac: expect-ast-min [[numeric-for]] [[1]]
local weak = setmetatable({}, {__mode="v"})
local observed
local old = getmetatable(_G)
setmetatable(_G, {__index=function(_, key)
    if key == "normal_binding_observe" then
        collectgarbage("collect")
        observed = weak[1] ~= nil
        return 0
    end
end})
local function check()
    for index = 1, 1, 1 do
        index = {}
        weak[1] = index
    end
    return normal_binding_observe
end
check()
setmetatable(_G,old)
print("binding-final",observed)
assert(observed == true)
