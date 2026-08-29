-- regress_374_path_condition_clean_islands#1: a clean structured prefix still specializes inside a goto-tainted proto
-- unluac: expect-contains [[if mark("inner", true) then]]
-- unluac: expect-not-contains [[not flag or mark("inner", true)]]

local events = {}

function mark(name, value)
    events[#events + 1] = name
    return value
end

local function clean_prefix(flag, start_right, cycle)
    for _ = 1, 1 do
        if flag then
            mark("outer", true)
            if not flag or mark("inner", true) then
                mark("body", true)
            end
        end
    end

    local x = 0
    local y = 0
    if start_right then
        goto right
    end

    ::left::
    x = x + 1
    y = y + 10
    if cycle and x < 3 then
        goto right
    end
    goto done

    ::right::
    x = x + 2
    y = y + 1
    if cycle and y < 13 then
        goto left
    end

    ::done::
    return x, y
end

local x, y = clean_prefix(true, true, false)
assert(x == 2 and y == 1, x .. "," .. y)
assert(table.concat(events, ",") == "outer,inner,body", table.concat(events, ","))

-- regress_374_path_condition_clean_islands#2: a closed multi-entry label graph cannot inherit lexical false facts
-- unluac: expect-contains [[if flag and mark("merge-true", "true") then]]

local function closed_merge(flag, jump_to_right, cycle)
    if jump_to_right then
        goto right
    end
    if flag then
        return "early-true"
    end

    ::left::
    if cycle then
        goto right
    end
    do
        return "left"
    end

    ::right::
    if flag and mark("merge-true", "true") then
        return "true"
    end
    mark("merge-false", false)
    if cycle then
        cycle = false
        goto left
    end
    return "false"
end

assert(closed_merge(true, true, false) == "true")
assert(closed_merge(false, false, false) == "left")
assert(table.concat(events, ",") == "outer,inner,body,merge-true", table.concat(events, ","))

-- regress_374_path_condition_clean_islands#3: a clean arm has one structured entry even when its sibling jumps to a label
-- unluac: expect-contains [[if mark("clean-arm", true) then]]
-- unluac: expect-not-contains [[not flag or mark("clean-arm", true)]]

local function clean_arm(flag, jump_right)
    local result = "none"
    if flag then
        if not flag or mark("clean-arm", true) then
            result = "clean"
        end
    elseif jump_right then
        goto right
    end
    goto done

    ::right::
    result = "right"

    ::done::
    return result
end

assert(clean_arm(true, false) == "clean")
assert(clean_arm(false, true) == "right")
assert(table.concat(events, ",") == "outer,inner,body,merge-true,clean-arm", table.concat(events, ","))

-- regress_374_path_condition_clean_islands#4: consecutive clean statements propagate fallthrough facts before a tainted graph
-- unluac: expect-not-contains [[flag and mark("clean-run", true)]]
-- unluac: expect-not-contains [[mark("clean-run", true)]]

local function clean_run(flag, jump_right, cycle)
    if flag then
        return "early"
    end
    if flag and mark("clean-run", true) then
        return "impossible"
    end

    local result
    if jump_right then
        goto right
    end

    ::left::
    if cycle then
        goto right
    end
    result = "left"
    goto done

    ::right::
    if cycle then
        cycle = false
        goto left
    end
    result = "right"

    ::done::
    return result
end

assert(clean_run(true, false, false) == "early")
assert(clean_run(false, false, false) == "left")
assert(clean_run(false, true, false) == "right")
assert(table.concat(events, ",") == "outer,inner,body,merge-true,clean-arm", table.concat(events, ","))
