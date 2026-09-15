-- regress_242_repeat_nested_break_shared_fallthrough: nested break不能把共享fallthrough错误并入外层branch
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(b, c)
    local x = 0
    repeat
        if b then
            x = x + 1
            if c then
                break
            end
        else
            x = x + 2
        end
        print("tail", x)
        x = x + 1
    until true
    return x
end

assert(run(false, false) == 3)
assert(run(true, false) == 2)
assert(run(true, true) == 1)
print("regress_242_repeat_nested_break_shared_fallthrough")
