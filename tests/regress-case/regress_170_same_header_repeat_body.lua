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

print("regress_170_same_header_repeat_body#1", run(false, true, 3))
