-- regress_294_luau_continue_shared_break_tail: if/elseif continue不能抢占while或repeat的共享break tail
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[<= 0]]
-- unluac: expect-not-contains [[ = 0]]
local function run_while(a, b, n)
    while n > 0 do
        n -= 1
        if not a then
            print("while-effect", n)
        elseif b then
            continue
        end
        if n == 1 then
            break
        end
    end
    return n
end

local function run_repeat(a, b, n)
    repeat
        n -= 1
        if not a then
            print("repeat-effect", n)
        elseif b then
            continue
        end
        if n == 1 then
            break
        end
    until n <= 0
    return n
end

local w1, w2, w3 = run_while(false, false, 3), run_while(true, true, 3), run_while(true, false, 3)
local r1, r2, r3 = run_repeat(false, false, 3), run_repeat(true, true, 3), run_repeat(true, false, 3)
assert(w1 == 1 and w2 == 0 and w3 == 1)
assert(r1 == 1 and r2 == 0 and r3 == 1)
print("regress_294_luau_continue_shared_break_tail", w1, w2, w3, r1, r2, r3)
