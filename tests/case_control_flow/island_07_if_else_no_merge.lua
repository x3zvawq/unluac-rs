-- regress_247_disconnected_if_else_no_merge: 终止/无限两臂没有 postdom merge
-- unluac: expect-contains [[if]]
-- unluac: expect-contains [[while true do]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]

local function run(flag)
    if flag then
        while true do
            print("running")
        end
    else
        return 1
    end
end

local function choose(flag)
    if flag then
        while true do
            print("left")
        end
    else
        while true do
            print("right")
        end
    end
end

assert(run(false) == 1)
assert(type(choose) == "function")
print("regress_247_disconnected_if_else_no_merge")

-- 通过第三次输出主动抛出标记，有限观察三个原本无限的分支。
local original_print = print
local function observe(fn, flag, label)
    local count = 0
    local stop = {}
    print = function(value)
        assert(value == label)
        count = count + 1
        if count == 3 then error(stop, 0) end
    end
    local ok, result = pcall(fn, flag)
    print = original_print
    assert(not ok and result == stop and count == 3)
end
observe(run, true, "running")
observe(run, 0, "running")
observe(choose, true, "left")
observe(choose, false, "right")
observe(choose, nil, "right")
assert(run(nil) == 1)
-- unluac: expect-ast-count [[while]] [[3]]
-- unluac: expect-ast-count [[repeat]] [[0]]
