-- regress_85_repeat_nested_numeric_body#1: nested numeric-for entry is repeat body, not while exit
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, xs)
    for _ in xs do
        repeat
            if a then
                for _ = 1, 3 do
                    print("regress_85_repeat_nested_numeric_body#1 body")
                    continue
                end
                break
            else
                for _ = 1, 3 do
                    print("regress_85_repeat_nested_numeric_body#1 else")
                    print("regress_85_repeat_nested_numeric_body#1 else")
                end
            end
        until a
    end
    return "done"
end

local function keep_while(b, xs)
    while not b do
        for _ in xs do
            continue
        end
        if xs[1] then
            break
        end
    end
    return "while"
end

local repeat_result = run(true, { true })
local while_result = keep_while(true, { true })
assert(repeat_result == "done" and while_result == "while")
print("regress_85_repeat_nested_numeric_body#1", repeat_result, while_result)
