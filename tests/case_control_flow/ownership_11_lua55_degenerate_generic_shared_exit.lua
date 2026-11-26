-- regress_260_lua55_degenerate_generic_shared_exit#1: 零次迭代出口与 body 出口共享 continuation
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[goto ]]
local function run(a, b, xs)
    local x = 0
    for _ in pairs(xs) do
        repeat
            x = x + 1
            x = x + 1
        until a and b
        break
    end
    return x
end

local empty = run(true, true, {})
local entered = run(true, true, { true })
assert(empty == 0 and entered == 2)
-- 多项输入也只进入第一次 body；假参数只能用于不会进入 repeat 的空表。
assert(run(0, "", {true, true, true}) == 2)
assert(run("", 0, {true, true}) == 2)
assert(run(false, false, {}) == 0)
assert(run(nil, true, {}) == 0)
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]]
print(
    "regress_260_lua55_degenerate_generic_shared_exit#1",
    empty,
    entered
)
