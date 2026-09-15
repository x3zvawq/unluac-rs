-- regress_262_infinite_loop_nearest_merge: 无限循环内分支按 CFG 近端选择 merge
-- unluac: expect-order [[print("near")]] [[print("far")]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]

local function run(side)
    while true do
        goto H

        ::K::
        print("far")
        goto L

        ::H::
        if side then
            print("left")
        else
            print("right")
        end

        ::J::
        print("near")
        goto K

        ::L::
        side = not side
    end
end

return run
