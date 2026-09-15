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
