-- RETURN 自带捕获关闭由函数作用域承接，不把整个 chunk 包进多余 do/end。
local function pair(value)
    return value, value + 1
end

local function check()
    local function terminal_values()
        local value = 7
        local function read()
            return value
        end
        local function change()
            value = 9
            return read
        end
        -- 先得到旧值，再改变同一 cell；返回后的闭包仍读取最终值。
        return read(), change(), read()
    end

    local function explicit_scope()
        local first
        do
            local value = 11
            first = function()
                return value
            end
        end
        local value = 22
        local function second()
            return value
        end
        -- 显式 CLOSE 仍隔离先前 cell，不能沿用终端 Return 的处理。
        return first(), second()
    end

    local events = {}
    local function resource_return()
        local value = "before"
        local function read()
            return value
        end
        local resource <close> = setmetatable({}, {
            __close = function()
                events[#events + 1] = read()
                value = "closed"
            end,
        })
        local function prepare()
            events[#events + 1] = "prepare:" .. read()
            return read
        end
        -- 两个返回值先求值，再执行 TBC；闭包返回后看见关闭回调的写入。
        return prepare(), read()
    end

    local first, read, last = terminal_values()
    assert(first == 7 and last == 9 and read() == 9)
    local old, new = explicit_scope()
    assert(old == 11 and new == 22)
    local closed, snapshot = resource_return()
    assert(snapshot == "before" and closed() == "closed")
    assert(table.concat(events, ",") == "prepare:before,before")
    local a, b = pair(3)
    assert(a == 3 and b == 4)
    print("regress_628_terminal_capture_scope", "OK")
    return "checked"
end
local first, second, third = pair(3)
print(first, second, third, check())
