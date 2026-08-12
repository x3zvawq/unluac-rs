-- regress_112_luau_continue_merge_state_owner#1: continue merge pad 保留嵌套 loop state owner
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[for r1_6, r1_7 in p1_3 do]]
local function run(a, b, c, xs)
    local x = 0
    while not b do
        if a then
            if xs[x] then
                print(x)
            end
            if a and b then
                break
            end
            while b do
                if a or c then
                    continue
                else
                    x = x + 1
                    x = x + 1
                end
            end
        else
            for i = 1, 3 do
                break
            end
            continue
        end
        if xs[x] then
            break
        end
        while not b do
            for k, v in xs do
                print(x)
                if xs[x] then
                    break
                end
            end
            break
        end
    end
    repeat
        if a then
            continue
        end
        repeat
            if a or c then
                if a and b then
                    x = x + 1
                end
                for k, v in xs do
                    x = x + 1
                    x = x + 1
                end
                continue
            else
                if a or c then
                    print(x)
                else
                    break
                end
            end
        until xs[x]
    until a or c
    return x
end

print("regress_112_luau_continue_merge_state_owner#1", run(true, true, false, {}))
