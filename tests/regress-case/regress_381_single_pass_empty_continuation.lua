-- regress_381_single_pass_empty_continuation: both fallthrough arms need no shared tail after cleanup
-- unluac: expect-not-contains [[repeat]]

local function run(first, stop)
    local events = {}
    repeat
        if first then
            if stop then
                break
            end
            events[#events + 1] = "then"
        else
            events[#events + 1] = "else"
        end
        local dead = 1
    until true
    return table.concat(events, ",")
end

assert(run(true, true) == "")
assert(run(true, false) == "then")
assert(run(false, true) == "else")
