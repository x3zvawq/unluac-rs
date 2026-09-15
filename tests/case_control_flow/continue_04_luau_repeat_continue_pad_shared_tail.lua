-- regress_117_luau_repeat_continue_pad_shared_tail#1: repeat continue pad 不消费共享 tail 与 condition
-- unluac: expect-contains [[continue]]
-- unluac: expect-contains [[#1", 6)]]
-- unluac: expect-not-contains [[                if p1_0 then]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, xs)
    local x = 0
    for i = 1, 3 do
        x = x + 1
        repeat
            if a then
                if xs[x] then break end
                if a then continue else x = x + 1 end
            end
            x = x + 1
        until b
    end
    return x
end

print("regress_117_luau_repeat_continue_pad_shared_tail#1", run(false, true, {}))
print("regress_117_luau_repeat_continue_pad_shared_tail#2", run(true, true, {}))
print("regress_117_luau_repeat_continue_pad_shared_tail#3", run(true, true, { [1] = true }))
