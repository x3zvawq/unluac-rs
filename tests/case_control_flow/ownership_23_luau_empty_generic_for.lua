-- regress_76_luau_empty_generic_for#1: Luau folds a continue-only generic-for body into its header
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[generic-for]] [[2]]
-- unluac: expect-ast-count [[repeat]] [[0]]
-- unluac: expect-ast-count [[while]] [[0]]
-- unluac: expect-ast-count [[local-binding]] [[6]]
local function drain(xs)
    local result = 0
    for _ in xs do
        repeat
            for _ in xs do
                continue
            end
        until result < 3
    end
    return result
end

local result = drain({ 1, 2, 3 })
assert(result == 0)
assert(drain({}) == 0)
local steps = 0
-- 每个 for 的 control 都独立从 nil 开始；外层和三次内层各请求四次。
assert(drain(function(_, control)
    steps = steps + 1
    local next_index = (control or 0) + 1
    if next_index <= 3 then
        return next_index
    end
end) == 0)
assert(steps == 16)
print("regress_76_luau_empty_generic_for#1", result)
