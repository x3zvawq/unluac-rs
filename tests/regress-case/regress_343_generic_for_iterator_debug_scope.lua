-- regress_343_generic_for_iterator_debug_scope: source iterator locals 保留可观察的 debug 作用域身份。
-- unluac: expect-contains [[local iterator = inspect_iterator_scope]]
-- unluac: expect-contains [[local state, control = nil, nil]]

local observed

local function inspect_iterator_scope()
    local names = {}
    local index = 1
    while true do
        local name = debug.getlocal(2, index)
        if name == nil then
            break
        end
        names[#names + 1] = name
        index = index + 1
    end
    observed = table.concat(names, ",")
    return nil
end

local function run()
    local iterator = inspect_iterator_scope
    local state = nil
    local control = nil
    for _ in iterator, state, control do
    end
    return observed:find("iterator", 1, true) ~= nil,
        observed:find("state", 1, true) ~= nil,
        observed:find("control", 1, true) ~= nil
end

print("regress_343_generic_for_iterator_debug_scope", run())
