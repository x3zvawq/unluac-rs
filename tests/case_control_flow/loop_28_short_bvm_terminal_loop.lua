-- regress_284_luau_short_bvm_terminal_loop: terminal guard不能让短路BVM丢失本轮共享tail
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[ or ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c, values)
    local x = 0
    for _ in pairs(values) do
        if a or b then
            if c then
                return x
            end
        else
            x = x + 1
        end
        print()
    end
    return x
end

local fallback = run(false, false, false, { 1 })
local terminal = run(true, false, true, { 1 })
assert(fallback == 1 and terminal == 0)
print("regress_284_luau_short_bvm_terminal_loop", fallback, terminal)
-- stdout 同时观察共享 tail：fallback 每轮加一，truthy guard 的非终结路径只打印。
assert(run(false, false, false, {1, 2, 3}) == 3)
assert(run(false, false, true, {1, 2, 3}) == 3)
assert(run(false, true, false, {1, 2, 3}) == 0)
assert(run(false, true, true, {1, 2, 3}) == 0)
assert(run(true, false, false, {1, 2, 3}) == 0)
assert(run(true, false, true, {1, 2, 3}) == 0)
assert(run(true, true, false, {1, 2, 3}) == 0)
assert(run(true, true, true, {1, 2, 3}) == 0)
assert(run(nil, false, true, {1, 2}) == 2)
assert(run(0, false, nil, {1, 2}) == 0)
assert(run(false, "", 0, {1, 2}) == 0)
assert(run("", false, "", {1, 2}) == 0)
assert(run(false, false, false, {}) == 0)
assert(run(true, true, true, {}) == 0)
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]]
