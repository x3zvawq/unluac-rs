-- regress_83_nested_break_exit_pad#1: nested branch chains belong to one break exit pad
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, xs)
    while not b do
        if a then
            if xs[1] then
                break
            end
        else
            continue
        end
        if a and b then
            break
        end
        break
    end
    print("regress_83_nested_break_exit_pad#1 done")
end

run(true, false, { true })
