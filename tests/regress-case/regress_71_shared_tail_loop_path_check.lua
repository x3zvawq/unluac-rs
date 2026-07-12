-- regress_71_shared_tail_loop_path_check#1: shared-tail path proof follows owned loop exits
-- unluac: expect-contains [[while #p1_1 >= r1_0 do]]
-- unluac: expect-contains [[print("shared-tail")]]
-- unluac: expect-not-contains [[goto]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]

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

print(
    "regress_71_shared_tail_loop_path_check#1",
    shared_tail_after_loop(true, { "next" })
)
