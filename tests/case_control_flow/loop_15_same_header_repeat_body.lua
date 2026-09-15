-- regress_170_same_header_repeat_body#1: outer repeat body 不能阻断 same-header 嵌套 loop 候选
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[while]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, state)
    repeat
        while a do
        end
        if state == 1 then
            state = 2
            break
        elseif state == 2 then
            state = 3
            break
        elseif state == 3 then
            print(state)
        end
        state = 4
    until b
    return state
end

local result = run(false, true, 3)
assert(result == 4)
-- 前移的常量准备不能覆盖 body 仍要读取的 state，break/continue 均观察原值。
assert(run(false, true, 1) == 2)
assert(run(false, true, 2) == 3)
assert(run(false, true, 0) == 4)
print("regress_170_same_header_repeat_body#1", result)
