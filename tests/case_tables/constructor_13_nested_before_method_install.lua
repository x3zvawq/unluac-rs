-- 嵌套表先按原容量完成初始化，再独立安装方法；两个 closure 复用原临时槽。
-- unluac: expect-contains [[values = {]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[local-function]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[7]] [[@proto=0]]
-- unluac: expect-contains [[local a, b, c, d = first(), first(), first(), first()]] [[@debug=retained]] [[@dialect=luau]]

local function make(start)
    local value = start
    local state = {
        index = 0,
        values = { [1] = nil, [2] = 3, [3] = nil, [4] = 2 },
    }
    function state:next()
        self.index = self.index + 1
        return self.values[self.index]
    end
    return function()
        value = value + (state:next() or 1)
        return value
    end
end

local first = make(10)
local second = make(20)
assert(first ~= second)
local a, b, c, d = first(), first(), first(), first()
assert(a == 11 and b == 14 and c == 15 and d == 17)
assert(second() == 21 and first() == 18)
print("nested-before-method", a, b, c, d, second())
