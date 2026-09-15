-- regress_09_loadnil_capture_range#1: Lua 5.2/5.3 LOADNIL 的 B 是从 A 开始的偏移，不能漏掉尾部 nil local
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-min [[function]] [[2]]
-- unluac: expect-ast-count [[table-list-field]] [[5]] [[@proto=0]]
local a, b, c, d, e = 1, 2, 3, nil, nil
local t = { a, b, c, d, e }
local s = table.pack(t)
assert(t[4] == nil and t[5] == nil and s.n == 1)
print("regress_09_loadnil_capture_range#1", t[4], t[5], s.n)

local f = function()
    return function()
        return print("regress_09_loadnil_capture_range#2", a, b, c, d, e)
    end
end

f()()

-- 两个 nil cell 后续独立变化，已构造的数组仍保留读取时的 nil 快照。
d = 41
assert(e == nil and t[4] == nil and t[5] == nil)
f()()
e = 42
assert(d == 41)
f()()
