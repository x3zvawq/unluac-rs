-- regress_71_shared_tail_loop_path_check#1: shared-tail path proof follows owned loop exits
-- unluac: expect-contains [[while #p1_1 >= r1_0 do]]
-- unluac: expect-contains [[print("shared-tail")]]
-- unluac: expect-not-contains [[goto]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[5]]

local function shared_tail_after_loop(enabled, values)
    if enabled then
        local index = 1
        while index <= #values do
            if values[index] == "stop" then
                return "early"
            end
            index = index + 1
        end
    else
        print("disabled")
    end
    print("shared-tail")
end

local result = shared_tail_after_loop(true, { "next" })
assert(result == nil)
print("regress_71_shared_tail_loop_path_check#1", result)

local saved_print, events = print, ""
print = function(message)
    events = events .. message .. ";"
end
assert(select("#", shared_tail_after_loop(false, nil)) == 0)
assert(events == "disabled;shared-tail;")
events = ""
assert(select("#", shared_tail_after_loop(0, {})) == 0 and events == "shared-tail;")
events = ""
assert(shared_tail_after_loop(true, { "stop", "next" }) == "early" and events == "")
assert(shared_tail_after_loop(true, { "next", "stop" }) == "early" and events == "")
assert(select("#", shared_tail_after_loop("", { "next", "next" })) == 0)
assert(events == "shared-tail;")
events = ""
assert(select("#", shared_tail_after_loop(nil, nil)) == 0)
assert(events == "disabled;shared-tail;")
print = saved_print
