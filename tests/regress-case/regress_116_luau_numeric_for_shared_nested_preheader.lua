-- regress_116_luau_numeric_for_shared_nested_preheader#1: numeric-for 内层 while 的共享 for preheader 先于 early continue
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c, xs)
    local x = 0
    if a and b then
        print(x)
        for i = 1, 3 do
            x = x + 1
            continue
        end
        if a and b then
            print(x)
        end
    end
    for i = 1, 3 do
        while not b do
            if a then
                for j = 1, 3 do
                    print(x)
                end
            else
                if a then
                    print(x)
                else
                    break
                end
                if a then continue end
            end
            print(x)
            for j = 1, 3 do
                while not b do
                    x = x + 1
                end
                repeat
                    break
                until not b
                if a and b then
                    x = x + 1
                end
            end
        end
        if a or c then
            if a and b then break end
            x = x + 1
            repeat
                if a or c then
                    continue
                else
                    x = x + 1
                    x = x + 1
                end
            until not b
        else
            if a then
                if xs[x] then break end
                while not b do
                    x = x + 1
                end
                repeat
                    x = x + 1
                    break
                until a and b
            else
                continue
            end
        end
    end
    return x
end

print("regress_116_luau_numeric_for_shared_nested_preheader#1", run(false, false, true, {}))
print("regress_116_luau_numeric_for_shared_nested_preheader#2", run(true, true, true, {}))
print("regress_116_luau_numeric_for_shared_nested_preheader#3", run(false, true, false, {}))
