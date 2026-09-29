-- regress_148_luau_repeat_recompile_state_owner#1: repeat 再编译后的中间 phi 继续归外层 loop state
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local subject = function(a, b, c, xs)
    local x = 0
    for _ in xs do
        repeat
            if a then
                print(x)
            elseif not b or not c then
                x = x + 1
                print(x)
                if x < 3 then
                    break
                end
            end
            print(x)
        until a
    end
    return x
end

local function check(name, a, b, c, xs, expected, trace, limit)
    local saved_print, log, stop = print, {}, {}
    print = function(value)
        log[#log + 1] = tostring(value)
        if limit and #log == limit then error(stop) end
    end
    local ok, result = pcall(subject, a, b, c, xs)
    print = saved_print
    if limit then
        assert(not ok and result == stop, name)
    else
        assert(ok and result == expected, name)
    end
    assert(table.concat(log, ",") == trace, name .. ": " .. table.concat(log, ","))
    print(name, ok, trace)
end

for _, a in ipairs({false, true}) do
    for _, b in ipairs({false, true}) do
        for _, c in ipairs({false, true}) do
            if a then
                check("normal", a, b, c, {4, 7}, 0, "0,0,0,0")
            elseif not b or not c then
                check("break", a, b, c, {4, 7}, 2, "1,2")
            else
                check("repeat", a, b, c, {4, 7}, nil, "0,0,0,0", 4)
            end
        end
    end
end
check("third_iteration", false, false, false, {4, 7, 9}, nil, "1,2,3,3,4,4,5,5", 8)
check("empty", false, true, true, {}, 0, "")
check("nil_condition", nil, 0, nil, {4, 7}, 2, "1,2")
check("truthy_zero", 0, nil, 0, {4, 7}, 0, "0,0,0,0")
check("zero_guards", false, 0, 0, {4, 7}, nil, "0,0,0,0", 4)
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[0]] [[@proto=1]]
return subject
