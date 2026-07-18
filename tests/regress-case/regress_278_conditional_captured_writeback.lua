-- regress_278_conditional_captured_writeback: nested条件中的写回不是无条件carried handoff
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(entry, spin, commit)
    local state = 1
    local function get_state()
        return state
    end

    if entry then
        goto second
    end

    ::first::
    if not spin then
        goto ready
    end

    ::second::
    if spin then
        spin = false
        goto first
    end

    ::ready::
    local next_state = state + 10
    if commit then
        state = next_state
    end
    return next_state, get_state()
end

local a, b = run(true, false, false)
local c, d = run(true, false, true)
print("regress_278_conditional_captured_writeback", a, b, c, d)
