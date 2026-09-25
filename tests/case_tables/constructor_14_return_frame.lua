-- 前一次 CALL 的结果写入上值后，返回构造器仍应在原槽分配并直接返回。
-- unluac: expect-contains [[return {}]]
-- unluac: expect-ast-count [[local-binding]] [[5]]
local count = 0
local function next_count(value, ...)
    return value + 1
end
-- 保持 Luau O2 的独立调用边界，以检查实际的返回帧。
local function empty(...)
    count = next_count(count)
    return {}
end

local first = empty()
first.marker = 7
local second = empty()
assert(count == 2 and first ~= second and first.marker == 7 and next(second) == nil)
print("constructor-return-frame", count, first.marker, next(second))
