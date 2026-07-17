-- regress_261_branch_shared_continuation_nearest: 共享 continuation 按 CFG 近端选择而非物理布局
-- unluac: expect-contains [[return "stop-a"]]
-- unluac: expect-contains [[return "stop-b"]]
-- unluac: expect-order [[print("near")]] [[print("far")]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]

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

print(run(false, true, true, false))
