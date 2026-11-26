-- regress_26_forward_capture_function_coalesce#1: closure 捕获的前向函数槽位保留独立 binding
local function make_callbacks(obj)
    local second
    local first = function(value)
        return second(obj, value + 1)
    end
    second = function(_, value)
        if value > 3 then
            return first(value - 1)
        end
        return obj.base + value
    end
    return first(1), second(nil, 1)
end

local first, second = make_callbacks({ base = 10 })
assert(first == 12 and second == 11)
print("regress_26_forward_capture_function_coalesce#1", first, second)
