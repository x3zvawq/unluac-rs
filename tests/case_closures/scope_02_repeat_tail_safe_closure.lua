-- A non-escaping nested closure keeps its repeat loop cleanly structured.
-- unluac: expect-ast-count [[repeat]] [[1]]

local function stop()
    collectgarbage("collect")
    return true
end

repeat
    do
        local value = {}
        local function hold()
            return value
        end
    end
until stop()

print("regress_459_repeat_tail_safe_closure", "OK")
