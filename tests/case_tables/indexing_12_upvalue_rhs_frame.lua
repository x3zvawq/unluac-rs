-- 上值字段写保留目标与 RHS 的读取顺序，元方法改写 cell 不影响已准备的值。
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]

local target
local value
local writes = {}

local function write()
    target[1] = value
end

local first = {}
local second = {}
local original = {}
local replacement = {}
target = first
value = original
setmetatable(first, {
    __newindex = function(destination, key, incoming)
        writes[#writes + 1] = incoming
        target = second
        value = replacement
        rawset(destination, key, incoming)
    end,
})

write()
assert(first[1] == original and second[1] == nil)
assert(#writes == 1 and writes[1] == original)
assert(target == second and value == replacement)
write()
assert(second[1] == replacement and #writes == 1)
print("upvalue-rhs-frame", "OK")
