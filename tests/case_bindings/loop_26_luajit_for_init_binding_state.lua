-- FORI的整数和浮点路径在skip判断前覆盖FOR_EXT，独立于三个control的保证。
-- unluac: expect-ast-min [[numeric-for]] [[1]]
local weak = setmetatable({}, {__mode = "v"})
local results = {}
local old = getmetatable(_G)
setmetatable(_G, {__index = function(_, key)
    if key == "for_binding_observe" then
        collectgarbage("collect")
        results[#results + 1] = tostring(weak[1] ~= nil)
        return 0
    end
end})
local function check(initial, limit)
    do
        local a, b, c, object = false, false, false, {}
        weak[1] = object
    end
    for index = initial, limit, 1 do end
    return for_binding_observe
end
check(9, 1)
check(9.125, 9.125)
check(9.125, 1)
setmetatable(_G, old)
local result = table.concat(results, ",")
print("numeric-binding-overwrite", result)
assert(result == "false,false,false")
