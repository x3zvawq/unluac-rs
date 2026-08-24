-- common_13_path_conditions#1: 写入会使参数路径事实失效
local function test_direct_write()
    local function run(flag, replacement)
        if flag then
            flag = replacement
            if flag then
                return "written-true"
            end
            return "written-false"
        end
        return "skipped"
    end

    print("common_13_path_conditions#1", run(true, true), run(true, false), run(false, true))
end

-- common_13_path_conditions#2: 引用捕获可以在调用中改写参数
local function test_reference_capture()
    local function run(flag)
        local function clear()
            flag = false
        end

        if flag then
            clear()
            if flag then
                return "bad"
            end
        end
        return flag
    end

    print("common_13_path_conditions#2", run(true), run(false))
end

-- common_13_path_conditions#3: truthy 原值不能替换成布尔 true
local function test_truthy_value()
    local function classify(value)
        if value then
            if value == true then
                return "boolean", value
            end
            return "truthy", value
        end
        return "falsey", value
    end

    print("common_13_path_conditions#3", classify("text"))
end

-- common_13_path_conditions#4: 稳定路径专门化不能丢掉逻辑条件中的调用
local function test_effectful_conditions()
    local function run(flag)
        local calls = 0

        local function probe(result)
            calls = calls + 1
            return result
        end

        local selected = 0
        if flag then
            if probe(false) or not flag then
                selected = 1
            else
                selected = 2
            end
            if probe(true) and flag then
                selected = selected + 4
            end
        end
        return calls, selected
    end

    local calls, selected = run(true)
    local skipped_calls, skipped = run(false)
    print("common_13_path_conditions#4", calls, selected, skipped_calls, skipped)
end

-- common_13_path_conditions#5: table 字段会在两次读取之间变化
local function test_mutable_lookup()
    local cell = { flag = true }
    local result = "skipped"

    if cell.flag then
        cell.flag = false
        if cell.flag then
            result = "bad"
        else
            result = "updated"
        end
    end

    print("common_13_path_conditions#5", result)
end

-- common_13_path_conditions#6: OR 真臂与 AND 假臂不能推断单个原子
local function test_disjunctions()
    local function score(a, b)
        local result = 0
        if a or b then
            result = result + 10
            if a then
                result = result + 1
            end
        end
        if not (a and b) then
            result = result + 20
            if a then
                result = result + 2
            end
        end
        return result
    end

    print("common_13_path_conditions#6", score(false, true), score(true, false), score(true, true))
end

-- common_13_path_conditions#7: break 后不能从 while 正常退出推断条件为假
local function test_loop_exit()
    local function run(flag, limit)
        local result = 0
        while flag do
            result = result + 1
            if result >= limit then
                break
            end
        end
        if flag then
            result = result + 10
        end
        return result
    end

    print("common_13_path_conditions#7", run(true, 2), run(false, 2))
end

test_direct_write()
test_reference_capture()
test_truthy_value()
test_effectful_conditions()
test_mutable_lookup()
test_disjunctions()
test_loop_exit()
