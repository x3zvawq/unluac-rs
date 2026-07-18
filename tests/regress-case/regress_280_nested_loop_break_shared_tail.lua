-- regress_280_nested_loop_break_shared_tail#1: active-loop break 与 sibling 路径共享 repeat tail
local function run(a, b, c, xs)
    local x = 0
    while a do
        repeat
            if b then
                if c then
                    break
                else
                    print(x)
                end
            end
            if a then
                break
            end
        until xs[x]
    end
    return x
end

print("regress_280_nested_loop_break_shared_tail#1", type(run))
