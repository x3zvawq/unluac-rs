-- regress_216_irreducible_linear_exit#1: island owns its single-entry observable exit chain
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local function run(start_x, start_y)
    local installed
    local x, y = start_x or 0, start_y or 0

    if x == 0 then
        goto left
    end
    goto right

    ::left::
    x = x + 1
    y = y + 10
    if x < 3 then
        goto right
    end

    (function()
        local function exported()
            return 42
        end
        installed = exported
    end)()
    goto done

    ::right::
    x = x + 2
    y = y + 1
    if y < 13 then
        goto left
    end

    ::done::
    print("regress_216_irreducible_linear_exit#1", x, y, installed and installed() or "skip")
    return x, y, installed
end

local x, y, installed = run()
assert(x == 4 and y == 21 and installed() == 42)
local right_x, right_y, skipped = run(1, 20)
assert(right_x == 3 and right_y == 21 and skipped == nil)
-- unluac: expect-ast-count [[goto]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[label]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[0]]
-- unluac: expect-ast-count [[repeat]] [[0]]
-- installed、x/y 与仅在安装分支执行的局部函数各有一个声明，不向入口泄漏空别名。
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
