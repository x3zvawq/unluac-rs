-- unluac: expect-ast-min [[repeat]] [[2]]
local d, e, f = 117
local g = 1

repeat
    local continue_inner = false
    repeat
        if d == 117 then
            d = 80
            e = 0
            continue_inner = true
            break
        elseif d == 80 then
            f = 1
            d = 111
            continue_inner = true
            break
        elseif d == 111 then
            repeat
                f, e = 2, 3
                g = g + 5
            until g < 128
            d = 2
        elseif d == 2 then
            print(g, e, f)
            break
        end
        continue_inner = true
    until true

    if not continue_inner then
        break
    end
until false
