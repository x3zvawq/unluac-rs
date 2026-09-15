-- unluac: expect-ast-min [[repeat]] [[2]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
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
-- 观察放在循环外，避免额外短路分支改变被测 continue 状态机。
assert(g == 6 and e == 3 and f == 2)
