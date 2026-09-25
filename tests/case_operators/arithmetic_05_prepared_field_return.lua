-- 算术的左右准备与末尾动态索引共享 scratch，不能把中间结果冻结成独立变量。
-- unluac: expect-ast-count [[local-binding]] [[8]]
-- unluac: expect-ast-count [[assign]] [[3]]
local stage = 0
local middle = setmetatable({}, { __add = function(_, right)
    assert(stage == 1 and right == 7)
    stage = 2
    return 99
end })
local left = setmetatable({}, { __add = function(_, right)
    assert(stage == 0 and right == 2)
    stage = 1
    return middle
end })
local object = { value = left }
local function update(self, ...)
    local args = { ... }
    self.value = self.value + #args + args[1]
    return self, args[#args]
end
local returned, last = update(object, 7, 11)
assert(returned == object and object.value == 99 and last == 11 and stage == 2)
print("prepared-field-return", "OK")
