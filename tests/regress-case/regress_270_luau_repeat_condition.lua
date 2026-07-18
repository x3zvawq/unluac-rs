-- regress_270_luau_repeat_condition#1: repeat 的 early-continue 不能丢掉条件状态写回
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

local function run(a, b, xs)
    local x = 0
    for i = 1, 3 do
        x += 1
        repeat
            local done
            if a then
                if xs[x] then
                    break
                end
                if a then
                    continue
                end
                x += 1
            end
            x += 1
            done = b
        until done
    end
    return x
end

print("regress_270_luau_repeat_condition#1", run(false, true, {}))
