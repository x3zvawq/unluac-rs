-- regress_373_loop_invariant_rhs: eventless stable dependencies may move into loop headers
-- unluac: expect-contains [[while not not p1_0 == true do]]
-- unluac: expect-contains [[until not not p2_0 == true]]

local function stable_while(flag)
    local count = 0
    local first = flag
    local second = not first
    local condition = not second
    if false then
        print(first, second, condition)
    end
    while condition == true do
        count = count + 1
        if count == 2 then
            break
        end
    end
    return count
end

assert(stable_while(true) == 2)

local function stable_repeat(flag)
    local count = 0
    local first = flag
    local second = not first
    local condition = not second
    if false then
        print(first, second, condition)
    end
    repeat
        count = count + 1
    until condition == true
    return count
end

assert(stable_repeat(true) == 1)
