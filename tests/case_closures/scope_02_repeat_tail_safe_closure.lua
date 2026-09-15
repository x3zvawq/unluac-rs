-- A non-escaping nested closure needs no extra do scope before an eventful repeat condition.
-- unluac: expect-not-contains [[  do]]
-- unluac: expect-ast-max [[do-block]] [[0]]
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
