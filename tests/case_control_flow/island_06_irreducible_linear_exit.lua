-- regress_216_irreducible_linear_exit#1: island owns its single-entry observable exit chain
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
-- installed、x/y 与仅在安装分支执行的局部函数各有一个声明，不向入口泄漏空别名。
