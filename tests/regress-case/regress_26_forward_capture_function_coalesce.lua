-- regress_26_forward_capture_function_coalesce#1: closure 捕获的前向函数槽位不能被 local-coalesce 合并
-- unluac: expect-contains [[local r1_0]]
-- unluac: expect-contains [[r1_0 = function]]
-- unluac: expect-contains [[return r1_1(1), r1_0(nil, 1)]]
-- unluac: expect-not-contains [[r1_1 = function]]
-- unluac: expect-not-contains [[unluac error]]
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

print("regress_26_forward_capture_function_coalesce#1", make_callbacks({ base = 10 }))
