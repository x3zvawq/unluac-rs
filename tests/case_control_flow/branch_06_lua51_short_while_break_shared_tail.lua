-- regress_292_lua51_short_while_break_shared_tail: 短路while的early break不能抢占非空共享tail
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-contains [[tail]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function checked(ok, i)
    print("condition", i)
    return assert(ok)
end

local function run(a, b)
    local i = 0
    while a and b or checked(i < 2, i) do
        i = i + 1
        if i == 2 then
            break
        end
        print("tail", i)
    end
    return i
end

local tt = run(true, true)
local tf = run(true, false)
local ft = run(false, true)
local ff = run(false, false)
assert(tt == 2, tt)
assert(tf == 2, tf)
assert(ft == 2, ft)
assert(ff == 2, ff)
print("regress_292_lua51_short_while_break_shared_tail", tt, tf, ft, ff)
