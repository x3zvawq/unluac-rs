-- regress_370_repeat_prefix_decision: an untouched prefix Decision does not own the repeat tail
-- unluac: expect-contains [[until stop() or again()]]
-- unluac: expect-not-contains [[unresolved]]

function stop()
    return true
end

function again()
    return false
end

local function run(a, b, c)
    repeat
        local x = 0
        if a then
            if c then
                x = x + 1
            end
            repeat
            until b
        end
        print(x)
        if stop() then
            break
        end
    until again()
end

run(true, true, true)
