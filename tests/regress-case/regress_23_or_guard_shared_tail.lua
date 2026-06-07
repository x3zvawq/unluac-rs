-- regress_23_or_guard_shared_tail#1: disjunctive guard false edges share one else tail
-- unluac: expect-contains [[else]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local state = {
    enabled = true,
    ready = true,
    override = false,
    count = 2,
}

local log = {}

local function mark(value)
    log[#log + 1] = value
end

local function or_guard_tail(flag, probe)
    if flag
        and (
            (state.override and probe.fast)
            or (
                state.enabled
                and probe ~= nil
                and (probe.active or state.ready)
                and state.count > 0
            )
        )
    then
        mark("hit")
    else
        mark("guard")
    end

    mark("tail")
    return table.concat(log, ",")
end

print("regress_23_or_guard_shared_tail#1", or_guard_tail(true, { active = false, fast = false }))
