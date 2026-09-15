-- regress_375_luau_constant_if_continue: removing a constant if keeps the selected continue's loop owner
-- unluac: expect-not-contains [[if true then]]
-- unluac: expect-contains [[continue]]

local function run()
    local count = 0
    while count < 2 do
        count += 1
        local chosen = 1 < 2
        if chosen then
            continue
        else
            count = 99
        end
    end
    return count
end

assert(run() == 2)
