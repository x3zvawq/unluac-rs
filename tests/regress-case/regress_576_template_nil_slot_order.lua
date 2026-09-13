-- 模板 nil 槽可恢复为运行时数组字段，但填充顺序不能跨过另一个运行时字段。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[table-set-list]]
local events = {}
local function left()
    events[#events + 1] = "left"
    return 1
end
local function right()
    events[#events + 1] = "right"
    return 2
end
local function empty()
end

local function forward()
    return {left(), right(), "tail"}
end
local function reversed()
    local values = {nil, nil, "tail"}
    values[2] = right()
    values[1] = left()
    return values
end
local function intervening_record()
    local values = {nil, "tail"}
    values.key = right()
    values[1] = left()
    return values
end
local function open_empty()
    return {left(), "tail", empty()}
end

local function show(label, values)
    print(label, table.concat(events, ","), #values,
        values[1], values[2], values[3], values.key)
    events = {}
end
show("regress_576#forward", forward())
show("regress_576#reverse", reversed())
show("regress_576#record-barrier", intervening_record())
show("regress_576#empty-tail", open_empty())

local function captured_read()
    local prefix = "before"
    local function change()
        prefix = "after"
        return 1
    end
    local values = {nil, prefix, "tail"}
    values[1] = change()
    return values[2], prefix
end
print("regress_576#read-before-change", captured_read())
