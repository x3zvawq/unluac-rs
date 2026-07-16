-- regress_243_repeat_tbc_iteration_scope: repeat 条件两侧的 CLOSE 属于每轮共享词法域
-- unluac: expect-contains [[<close>]]

local closed = 0
local closer = setmetatable({}, {
    __close = function()
        closed = closed + 1
    end,
})

local i = 0
repeat
    i = i + 1
    local unused <close> = closer
until i == 2
assert(closed == 2)

i = 0
repeat
    i = i + 1
    closer.done = i == 2
    local state <close> = closer
until state.done
assert(closed == 4)

i = 0
repeat
    i = i + 1
    local break_guard <close> = closer
    if i == 2 then
        break
    end
until false
assert(closed == 6)

print("regress_243_repeat_tbc_iteration_scope")
