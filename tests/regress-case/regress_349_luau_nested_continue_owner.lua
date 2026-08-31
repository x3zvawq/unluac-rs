-- regress_349_luau_nested_continue_owner: nested continue belongs to the inner loop and must not block folding the outer repeat tail
-- unluac: expect-contains [[until not p1_1 and p1_2 or p1_3]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-not-contains [[if p1_1 then]]
-- unluac: expect-not-contains [[if p1_2 then]]
-- unluac: expect-contains [[if not p2_1 then]]
-- unluac: expect-not-contains [[until true]]
local function run(skip_inner, skip_outer, stop, latch)
    repeat
        for index = 1, 3 do
            if skip_inner and index == 2 then
                continue
            end
            print("visit", index)
        end
        if skip_outer then
            continue
        end
        if stop then
            break
        end
    until latch
    return "done"
end

assert(run(true, true, false, true) == "done")
assert(run(false, false, true, false) == "done")
assert(run(false, false, false, true) == "done")

local function run_single_pass(skip_inner, stop)
    repeat
        for index = 1, 3 do
            if skip_inner and index == 2 then
                continue
            end
            print("single-visit", index)
        end
        if stop then
            break
        end
        print("single-tail")
    until true
    return "single-done"
end

assert(run_single_pass(true, true) == "single-done")
assert(run_single_pass(false, false) == "single-done")
