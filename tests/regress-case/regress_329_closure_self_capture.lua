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
