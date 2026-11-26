-- regress_242_repeat_nested_break_shared_fallthrough: nested break不能把共享fallthrough错误并入外层branch
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
local function run(b, c)
    local x = 0
    repeat
        if b then
            x = x + 1
            if c then
                break
            end
        else
            x = x + 2
        end
        print("tail", x)
        x = x + 1
    until true
    return x
end

assert(run(false, false) == 3)
assert(run(true, false) == 2)
assert(run(true, true) == 1)
local saved_print = print
local tail_count, tail_value = 0, nil
print = function(label, value)
    assert(label == "tail")
    tail_count, tail_value = tail_count + 1, value
end
assert(run(false, true) == 3 and tail_count == 1 and tail_value == 2)
assert(run(0, nil) == 2 and tail_count == 2 and tail_value == 1)
assert(run("", 0) == 1 and tail_count == 2)
assert(run(nil, "") == 3 and tail_count == 3 and tail_value == 2)
print = saved_print
print("regress_242_repeat_nested_break_shared_fallthrough")
