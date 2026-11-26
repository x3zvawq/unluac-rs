-- regress_375_constant_if_loop_control: removing a constant if keeps the selected break's loop owner
-- unluac: expect-not-contains [[if true then]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]

local function run()
    local count = 0
    while true do
        local chosen = 1 < 2
        if chosen then
            break
        else
            count = 99
        end
    end
    return count
end

assert(run() == 0)
