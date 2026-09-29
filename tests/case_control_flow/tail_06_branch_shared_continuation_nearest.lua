-- regress_261_branch_shared_continuation_nearest: 共享 continuation 按 CFG 近端选择而非物理布局
-- unluac: expect-contains [[return "stop-a"]]
-- unluac: expect-contains [[return "stop-b"]]
-- unluac: expect-order [[print("near")]] [[print("far")]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[if]] [[5]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[5]]

local function run(route, side, near_a, near_b)
    if route == 1 then
        goto K
    elseif route == 2 then
        goto J
    end
    goto H

    ::K::
    print("far")
    goto L

    ::H::
    if side then
        if near_a then
            goto J
        end
        return "stop-a"
    else
        if near_b then
            goto J
        end
        return "stop-b"
    end

    ::J::
    print("near")
    goto K

    ::L::
    return "done"
end

local result = run(false, true, true, false)
assert(result == "done")
print(result)

local saved_print, events = print, ""
print = function(message)
    events = events .. message .. ";"
end
local function check(route, side, near_a, near_b, expected, expected_events)
    events = ""
    assert(run(route, side, near_a, near_b) == expected)
    assert(events == expected_events)
end
check(1, false, false, false, "done", "far;")
check(2, false, false, false, "done", "near;far;")
check(0, true, true, false, "done", "near;far;")
check(0, true, false, true, "stop-a", "")
check(0, false, false, true, "done", "near;far;")
check(0, false, true, false, "stop-b", "")
check(nil, 0, "", nil, "done", "near;far;")
check("1", nil, true, nil, "stop-b", "")
print = saved_print
