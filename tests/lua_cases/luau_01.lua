-- luau_01#1: continue与复合运算管线
local function test_continue_compound()
    local function build_report(seed: number, items: { number }): string
        local acc: number = seed
        local marks = {}

        for index, value in ipairs(items) do
            if value % 3 == 0 then
                acc += index
                continue
            end

            local delta = if value > index then value - index else index - value
            acc += delta
            marks[#marks + 1] = `#{index}:{acc}`
        end

        return `seed={seed} acc={acc} marks={table.concat(marks, ",")}`
    end

    print("luau_01#1", build_report(5, { 4, 6, 9, 7, 12, 15, 3, 11 }))
end

-- luau_01#2: if表达式路由
local function test_if_expression()
    local function make_router(flag: boolean, offset: number)
        return function(name: string?, values: { number }): string
            local total: number = 0

            for index, value in ipairs(values) do
                local weight = if flag then index + offset else offset - index
                total += value * weight
            end

            local label = if name then name else "anon"
            local mode = if total > 0 then "pos" elseif total == 0 then "zero" else "neg"
            return `router {label} {mode} {total}`
        end
    end

    local run_a = make_router(true, 3)
    local run_b = make_router(false, 6)

    print("luau_01#2", run_a("alpha", { 2, 5, 1, 4 }))

    print("luau_01#2", run_b(nil, { 3, 1, 2 }))

end

-- luau_01#3: 字符串插值转义
local function test_interp_escape()
    local function decorate(tag: string, value: number): string
        local parity = if value % 2 == 0 then "even" else "odd"
        local body = `{tag}:{parity}:{value}`
        return `[{body}] len={#body} brace=\{}`
    end

    local pieces = {}

    for i = 1, 5 do
        if i == 2 then
            continue
        end

        pieces[#pieces + 1] = decorate(`item-{i}`, i * i - 1)
    end

    print("luau_01#3", table.concat(pieces, "|"))
end

-- luau_01#4: 类型标注回调交叉
local function test_typed_callback()
    local function simulate(
        seed: number,
        values: { number },
        step: (number, number, number) -> number
    ): string
        local history = {}
        local acc: number = seed

        for index, value in ipairs(values) do
            acc = step(acc, value, index)
            history[#history + 1] = acc
        end

        return `sim {table.concat(history, ",")} final={acc}`
    end

    local report = simulate(4, { 3, 9, 2, 8, 5 }, function(acc: number, value: number, index: number): number
        local next_value = if index % 2 == 0 then acc + value else acc - value + index
        return next_value
    end)

    print("luau_01#4", report)

end

-- luau_01#5: repeat内continue漏斗
local function test_repeat_continue()
    local function funnel(limit: number): string
        local i: number = 0
        local acc: number = 1
        local seen = {}

        repeat
            i += 1

            if i % 2 == 0 then
                acc += i
                continue
            end

            acc *= i
            seen[#seen + 1] = tostring(acc)
        until i >= limit

        return `repeat {acc} {table.concat(seen, ":")}`
    end

    print("luau_01#5", funnel(7))

end

-- luau_01#6: 复合索引副作用
local function test_compound_index()
    local slots = { 3, 7, 11, 13 }
    local cursor: number = 0

    local function next_index(): number
        cursor += 1
        return if cursor % #slots == 0 then #slots else cursor % #slots
    end

    for turn = 1, 6 do
        slots[next_index()] += if turn % 2 == 0 then turn * 2 else turn
    end

    print("luau_01#6", cursor, table.concat(slots, ","))
end

-- luau_01#7: 泛型折叠分支
local function test_generic_fold()
    local function fold<T>(items: { T }, seed: T, reducer: (T, T, number) -> T): T
        local acc = seed

        for index, item in ipairs(items) do
            acc = reducer(acc, item, index)
        end

        return acc
    end

    local result = fold({ 5, 2, 9, 1 }, 4, function(acc: number, item: number, index: number): number
        return if index % 2 == 0 then acc + item * index else acc - item + index
    end)

    print("luau_01#7", `luau-generic {result}`)

end

-- luau_01#8: 可选闭包分发
local function test_optional_closure()
    local function make_dispatch(prefix: string?)
        local counter: number = 0

        return function(values: { number }): string
            local parts = {}

            for index, value in ipairs(values) do
                if value < 0 then
                    counter += -value
                    continue
                end

                counter += value
                parts[#parts + 1] = if prefix then `{prefix}-{index}:{counter}` else `slot-{index}:{counter}`
            end

            return table.concat(parts, "|")
        end
    end

    local dispatch = make_dispatch("luau")
    print("luau_01#8", dispatch({ 4, -2, 7, 3, -1, 5 }))

end

-- luau_01#9: 递归if插值
local function test_recursive_if()
    local function cascade(depth: number, bias: number): number
        return if depth <= 1
            then bias
            else depth + cascade(depth - 1, bias + (if depth % 2 == 0 then 2 else -1))
    end

    local outputs = {}

    for i = 3, 6 do
        outputs[#outputs + 1] = `{i}:{cascade(i, i % 3)}`
    end

    print("luau_01#9", table.concat(outputs, ","))
end

-- luau_01#10: 嵌套continue闭包交叉
local function test_nested_continue()
    local function make_mesh(seed: number): () -> string
        local total: number = seed
        local captures = {}

        for row = 1, 4 do
            local inner: number = row

            for col = 1, 5 do
                if (row + col) % 3 == 0 then
                    total += row
                    continue
                end

                inner += col
                total += if inner % 2 == 0 then inner else col
            end

            local saved_row: number = row
            local saved_inner: number = inner
            local saved_total: number = total
            captures[#captures + 1] = function(): string
                return `r{saved_row}:{saved_inner}:{saved_total}`
            end
        end

        return function(): string
            local out = {}

            for index, capture in ipairs(captures) do
                out[index] = capture()
            end

            return table.concat(out, ";")
        end
    end

    print("luau_01#10", make_mesh(10)())

end

test_continue_compound()
test_if_expression()
test_interp_escape()
test_typed_callback()
test_repeat_continue()
test_compound_index()
test_generic_fold()
test_optional_closure()
test_recursive_if()
test_nested_continue()
