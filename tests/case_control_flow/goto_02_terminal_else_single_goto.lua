-- regress_364_terminal_else_single_goto: a single fallback goto can become the terminal else arm
-- 状态 carrier 合并后不再要求机械交接；入口跳转仍须越过 first 的写入到达 second。
-- unluac: expect-order [[goto ]] [[= 100]]
-- unluac: expect-ast-count [[goto]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[label]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[3]] [[@proto=1]]
-- 两次原加法都须保留；第一项同时匹配 + 1 和 + 10。
-- unluac: expect-count [[ + 1]] [[2]]
-- unluac: expect-count [[ + 10]] [[1]]

-- unluac: expect-not-contains [[unresolved]]

local function run(entry, first_exit, second_exit, cycle)
    local value = 0
    if entry then
        goto second
    end

    ::first::
    if first_exit then
        goto done
    end
    value = value + 1

    ::second::
    value = 100
    if second_exit then
        goto done
    end
    value = value + 10
    if cycle then
        goto first
    end

    ::done::
    return value
end

assert(run(true, false, true, false) == 100)
assert(run(false, true, false, false) == 0)
assert(run(false, false, true, false) == 100)
-- first_exit=false、second_exit=false、cycle=true 会永久循环；其余组合均终止。
for mask = 0, 15 do
    local entry = mask % 2 == 1
    local first_exit = math.floor(mask / 2) % 2 == 1
    local second_exit = math.floor(mask / 4) % 2 == 1
    local cycle = mask >= 8
    if first_exit or second_exit or not cycle then
        local want = 110
        if not entry and first_exit then
            want = 0
        elseif second_exit then
            want = 100
        end
        assert(run(entry, first_exit, second_exit, cycle) == want)
    end
end
assert(run(nil, 0, false, false) == 0)
assert(run(0, false, nil, false) == 110)
