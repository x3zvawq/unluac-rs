local co = coroutine.create(function(seed)
    local value = seed

    for step = 1, 2 do
        value = value + step
        coroutine.yield(value)
    end

    return value * 2
end)

local _, first = coroutine.resume(co, 10)
local _, second = coroutine.resume(co)
local _, third = coroutine.resume(co)

print("co", first, second, third, coroutine.status(co))
