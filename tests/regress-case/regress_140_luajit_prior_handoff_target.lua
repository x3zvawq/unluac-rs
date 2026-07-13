-- regress_140_luajit_prior_handoff_target#1: 前置goto臂写过的temp不能当成新handoff target
local state = 0
local total = 1

repeat
    local again = false
    repeat
        if state == 0 then
            state = 1
            again = true
            break
        elseif state == 1 then
            state = 2
            again = true
            break
        elseif state == 2 then
            repeat
                total = total + 5
            until total < 128
            state = 3
        elseif state == 3 then
            print("regress_140_luajit_prior_handoff_target#1", total)
            break
        end
        again = true
    until true

    if not again then
        break
    end
until false
