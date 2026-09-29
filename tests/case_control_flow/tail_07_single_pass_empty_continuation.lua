-- regress_381_single_pass_empty_continuation: both fallthrough arms need no shared tail after cleanup
-- unluac: expect-not-contains [[repeat]]
-- 原 LOADK 对应未使用的局部初始化；去掉单次循环壳不能顺便删除这次写入。
-- unluac: expect-contains [[ = 1]]
-- unluac: expect-ast-count [[local-binding]] [[3]]

local function run(first, stop)
    local events = {}
    repeat
        if first then
            if stop then
                break
            end
            events[#events + 1] = "then"
        else
            events[#events + 1] = "else"
        end
        local dead = 1
    until true
    return table.concat(events, ",")
end

assert(run(true, true) == "")
assert(run(true, false) == "then")
assert(run(false, true) == "else")
assert(run(false, false) == "else")
assert(run(0, "") == "")
assert(run(0, nil) == "then")
assert(run(nil, 0) == "else")
