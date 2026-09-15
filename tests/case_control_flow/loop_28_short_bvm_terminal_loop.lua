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
