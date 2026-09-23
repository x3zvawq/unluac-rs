-- 自引用闭包在独立词法域中建立；后继 for 控制区复用其槽，兼顾引用与按值捕获。
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=0]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=0]]
-- unluac: expect-contains [[= (function(]]
local exported = {}
do
    local function recur(n)
        if n == 0 then return 7 end
        return recur(n - 1)
    end
    exported[1] = function(n) return recur(n) end
end
for i = (function(value) return value end)(1), 2 do
    exported[i + 1] = function(value) return i + value end
end
assert(exported[1](3) == 7 and exported[2](4) == 5 and exported[3](4) == 6)
print("recursive-scope-frame", exported[1](0), exported[2](9), exported[3](9))
