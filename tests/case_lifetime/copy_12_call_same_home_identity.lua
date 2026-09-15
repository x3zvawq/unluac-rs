local weak = setmetatable({}, { __mode = 'v' })
local function hold(make)
    local a = make()
    local b = a
    b = a
    a = nil
    collectgarbage('collect')
    assert(b == weak[1] and b ~= nil, 'live')
    b = nil
    collectgarbage('collect')
    assert(weak[1] == nil, 'released')
end
hold(function()
    local object = {}
    weak[1] = object
    return object
end)
print('same-home-alias', 'OK')
