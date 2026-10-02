-- regress_381_single_pass_empty_continuation: 单次壳的共享尾写仍须服从提前 break。
-- 原 LOADK 对应未使用的局部初始化；共享尾并非空，不能为移除 repeat 删除这次写入。
-- unluac: expect-contains [[ = 1]]
-- unluac: expect-ast-count [[local-binding]] [[3]]
-- 表在单次壳之前建立，不需要外层空声明与壳内分离赋值。
-- unluac: expect-ast-count [[empty-local]] [[0]]

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
