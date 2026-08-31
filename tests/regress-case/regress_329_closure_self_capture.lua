-- regress_329_closure_self_capture#1: 递归 closure 覆盖 loop binding 时 capture 与写入目标必须保持同一身份
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function recurse_through_loop_binding()
    for binding = 1, 1 do
        binding = function(depth)
            if depth == 0 then
                return "done"
            end
            return binding(depth - 1)
        end
        return binding(3)
    end
end

assert(recurse_through_loop_binding() == "done")
print("regress_329_closure_self_capture#1", recurse_through_loop_binding())

-- regress_329_closure_self_capture#2: numeric-for 每轮 capture 必须写回当前 binding，且 CLOSE 后各轮身份独立
local function capture_each_loop_binding()
    local closures = {}
    for binding = 1, 3 do
        closures[binding] = function(delta)
            if delta ~= nil then
                binding = binding + delta
            end
            return binding
        end
    end
    return closures
end

local closures = capture_each_loop_binding()
assert(closures[1](10) == 11)
assert(closures[2]() == 2)
assert(closures[3](-1) == 2)
assert(closures[1]() == 11)
print(
    "regress_329_closure_self_capture#2",
    closures[1](),
    closures[2](),
    closures[3]()
)
