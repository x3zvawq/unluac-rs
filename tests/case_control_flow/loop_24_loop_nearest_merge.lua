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

-- 实际执行三个完整迭代，再以独立标记终止；观察器不能把运行错误当成正常退出。
local original_print = print
for start = 1, 2 do
    local trace, stop = {}, {}
    print = function(value)
        if #trace == 9 then error(stop, 0) end
        trace[#trace + 1] = value
    end
    local ok, message = pcall(run, start == 1)
    print = original_print
    assert(not ok and message == stop)
    if start == 1 then
        assert(table.concat(trace, ",") == "left,near,far,right,near,far,left,near,far")
    else
        assert(table.concat(trace, ",") == "right,near,far,left,near,far,right,near,far")
    end
end
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- 原入口的七个声明已足够，分支中的断言调用不应引入新的准备载体。
-- unluac: expect-ast-count [[local-binding]] [[7]] [[@proto=0]]

return run
