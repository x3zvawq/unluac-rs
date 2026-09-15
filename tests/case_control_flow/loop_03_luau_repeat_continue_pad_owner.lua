-- regress_119_luau_repeat_continue_pad_owner#1: repeat 的透明 continue pad 由分支臂消费
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(b)
    repeat
        while not b do break end
    until b
    return true
end

print("regress_119_luau_repeat_continue_pad_owner#1", run(true))
