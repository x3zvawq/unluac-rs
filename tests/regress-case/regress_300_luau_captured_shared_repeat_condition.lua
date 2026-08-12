-- regress_300_luau_captured_shared_repeat_condition: repeat body local在until条件中仍可见
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local value = _G

repeat_attempts = 0
function stop_repeat()
    repeat_attempts += 1
    return repeat_attempts > 2
end

repeat
    local function factory()
        return function()
            return value
        end
    end
until stop_repeat() or factory() == factory()

print("regress_300_result", repeat_attempts)
