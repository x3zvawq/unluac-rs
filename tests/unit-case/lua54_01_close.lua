-- lua54_01_close#1: to-be-closed基础
local function test_tbc_basic()
    local log = {}

    local function make_resource(name)
        return setmetatable({
            name = name,
        }, {
            __close = function(self, err)
                log[#log + 1] = self.name .. ":" .. tostring(err == nil)
            end,
        })
    end

    do
        local resource <close> = make_resource("res")
        log[#log + 1] = "body:" .. resource.name
    end

    print("lua54_01_close#1", table.concat(log, "|"))
end

-- lua54_01_close#2: to-be-closed多出口
local function test_tbc_multi_exit()
    local log = {}

    local function make_resource(name)
        return setmetatable({
            name = name,
        }, {
            __close = function(self, err)
                log[#log + 1] = self.name .. ":" .. tostring(err == nil)
            end,
        })
    end

    local function consume(mode)
        local out = {}

        do
            local first <close> = make_resource("first:" .. mode)
            out[#out + 1] = first.name

            while true do
                local second <close> = make_resource("second:" .. mode)
                out[#out + 1] = second.name

                if mode == "return" then
                    return out
                end

                if mode == "break" then
                    break
                end

                out[#out + 1] = first.name .. "+" .. second.name
                break
            end

            out[#out + 1] = "after:" .. first.name
        end

        return out
    end

    print("lua54_01_close#2", table.concat(consume("break"), ","))

    print("lua54_01_close#2", table.concat(consume("return"), ","))

    print("lua54_01_close#2", table.concat(log, "|"))

end

-- lua54_01_close#3: goto重入与close
local function test_tbc_goto_reenter()
    local log = {}

    local function make_resource(name)
        return setmetatable({
            name = name,
        }, {
            __close = function(self, err)
                log[#log + 1] = self.name .. ":" .. tostring(err == nil)
            end,
        })
    end

    local turn = 1

    do
        local outer <close> = make_resource("outer")

        ::again::
        do
            local inner <close> = make_resource("inner:" .. turn)
            if turn < 3 then
                turn = turn + 1
                goto again
            end

            log[#log + 1] = outer.name .. "+" .. inner.name
        end
    end

    print("lua54_01_close#3", table.concat(log, "|"))

end

-- lua54_01_close#4: close与尾调用屏障
local function test_close_tailcall()
    local log = {}

    local function make_resource(name)
        return setmetatable({
            name = name,
        }, {
            __close = function(self, err)
                log[#log + 1] = self.name .. ":" .. tostring(err == nil)
            end,
        })
    end

    local function invoke(fn, ...)
        return fn(...)
    end

    local function finalize(tag, mode, ...)
        local resource <close> = make_resource(tag)

        local function build(...)
            local parts = { ... }
            parts[#parts + 1] = resource.name
            return table.concat(parts, ":")
        end

        if mode == "tail" then
            return invoke(build, ...)
        end

        return build(...)
    end

    print("lua54_01_close#4", finalize("alpha", "tail", "x", "y"))

    print("lua54_01_close#4", finalize("beta", "plain", "m"))

    print("lua54_01_close#4", table.concat(log, "|"))

end

-- lua54_01_close#5: 泛型for与const close
local function test_for_const_close()
    local log = {}

    local function make_resource(name)
        return setmetatable({
            name = name,
        }, {
            __close = function(self, err)
                log[#log + 1] = self.name .. ":" .. tostring(err == nil)
            end,
        })
    end

    local function list_iter(values)
        local index = 0
        return function()
            index = index + 1
            if index <= #values then
                return index, values[index], #values - index
            end
        end
    end

    local out = {}

    for index, value, remaining in list_iter({ "aa", "bbb", "c" }) do
        local prefix <const> = value .. ":" .. index
        do
            local resource <close> = make_resource(prefix)
            if remaining % 2 == 0 then
                out[#out + 1] = resource.name .. ":even"
            else
                out[#out + 1] = resource.name .. ":odd"
            end
        end
    end

    print("lua54_01_close#5", table.concat(out, "|"))

    print("lua54_01_close#5", table.concat(log, "|"))

end

-- lua54_01_close#6: 参数alias不能取代to-be-closed绑定身份
local function test_tbc_param_binding()
    local closed
    local resource = setmetatable({ name = "parameter" }, {
        __close = function(self)
            closed = self.name
        end,
    })

    local function consume(value)
        local owned <close> = value
        return owned.name
    end

    local name = consume(resource)
    assert(name == "parameter")
    assert(closed == "parameter")
    print("lua54_01_close#6", name, closed)
end

-- lua54_01_close#7: 参数alias不能提前释放原参数槽的GC root
local function test_param_alias_gc_root()
    local function survives_alias_write(value)
        local alias = value
        local weak = setmetatable({ value }, { __mode = "v" })
        local turns = 0
        while turns < 1 do
            turns = turns + 1
            if alias == nil then
                return false, false
            end
            alias = {}
        end
        collectgarbage("collect")
        return weak[1] ~= nil, alias ~= nil
    end

    local alive, alias_alive = survives_alias_write({})
    assert(alive)
    assert(alias_alive)
    print("lua54_01_close#7", alive, alias_alive)
end

-- lua54_01_close#8: table seed覆盖必须先于字段RHS
local function test_table_seed_overwrite_order()
    local finalized = 0
    local observed
    local function make_old_value()
        return setmetatable({}, {
            __gc = function()
                finalized = finalized + 1
            end,
        })
    end
    local function observe_collection()
        collectgarbage("collect")
        observed = finalized
        return "value"
    end

    local table_value = make_old_value()
    local turns = 0
    while turns < 1 do
        turns = turns + 1
        table_value = {}
        table_value.field = observe_collection()
    end
    assert(observed == 1)
    print("lua54_01_close#8", observed, table_value.field)
end

-- lua54_01_close#9: constructor producer不能删除已有local的覆盖
local function test_constructor_producer_overwrite_order()
    local finalized = 0
    local function make_old_value()
        return setmetatable({}, {
            __gc = function()
                finalized = finalized + 1
            end,
        })
    end
    local function replacement()
        collectgarbage("collect")
        assert(finalized == 0)
        return "replacement"
    end

    local old = make_old_value()
    assert(old ~= nil)
    local table_value = {}
    old = replacement()
    table_value.field = old
    collectgarbage("collect")
    assert(finalized == 1)
    print("lua54_01_close#9", finalized, table_value.field)
end

-- lua54_01_close#10: nil数组槽不能被折叠成带空洞的构造器
local function test_nil_array_hole_length()
    local table_value = {}
    table_value[1] = nil
    table_value[2] = 1
    assert(#table_value == 0)
    print("lua54_01_close#10", #table_value)
end

-- lua54_01_close#11: 运行时 nil 也不能被当成已填充的数组槽
local function test_runtime_nil_array_hole()
    local function maybe_nil()
        return nil
    end
    local value = maybe_nil()
    local table_value = {}
    table_value[1] = value
    table_value[2] = 1
    assert(#table_value == 0)
    print("lua54_01_close#11", #table_value)
end

-- lua54_01_close#12: 非 nil 构造器值不能跨整数键重排副作用
local function test_integer_write_order()
    local order = {}
    local function mark(value)
        order[#order + 1] = value
        return {}
    end
    local table_value = {}
    table_value[2] = mark("second")
    table_value[1] = mark("first")
    assert(order[1] == "second" and order[2] == "first")
    print("lua54_01_close#12", order[1], order[2])
end

-- lua54_01_close#13: 被折入构造器的 producer 仍须保留对象 root
local function test_constructor_producer_root_lifetime()
    local finalized = 0
    local function make_gc_value()
        return setmetatable({}, {
            __gc = function()
                finalized = finalized + 1
            end,
        })
    end

    local value = make_gc_value()
    local table_value = { value }
    table_value[1] = nil
    collectgarbage("collect")
    assert(finalized == 0)
    print("lua54_01_close#13", finalized, table_value[1])
end

-- lua54_01_close#14: constructor不能删除独立producer local的强引用
local function test_constructor_independent_producer_root()
    local finalized = 0
    local function make_gc_value()
        return setmetatable({}, {
            __gc = function()
                finalized = finalized + 1
            end,
        })
    end

    local value = make_gc_value()
    local table_value = {}
    table_value[1] = value
    rawset(table_value, 1, nil)
    collectgarbage("collect")
    assert(finalized == 0)
    print("lua54_01_close#14", finalized, table_value[1])
end

-- lua54_01_close#15: seed尾部的运行时nil不能在后续SETLIST后变成已填充数组槽
local function test_fixed_setlist_combined_nil_shape()
    local first = nil
    local table_value = { first }
    table_value[2] = 1
    assert(#table_value == 0)
    print("lua54_01_close#15", #table_value)
end

-- lua54_01_close#16: 多级alias的producer仍须保留强引用到table清空之后
local function test_constructor_alias_root_lifetime()
    local finalized = 0
    local function make_gc_value()
        return setmetatable({}, {
            __gc = function()
                finalized = finalized + 1
            end,
        })
    end

    local table_value = {}
    local first = make_gc_value()
    local second = first
    local third = second
    table_value[1] = third
    rawset(table_value, 1, nil)
    collectgarbage("collect")
    assert(finalized == 0)
    print("lua54_01_close#16", finalized)
end

-- lua54_01_close#17: 无显式读取的call结果仍是同槽清空前的GC root
local function test_unused_call_result_root_lifetime()
    local finalized = 0
    local function make_gc_value()
        return setmetatable({}, {
            __gc = function()
                finalized = finalized + 1
            end,
        })
    end

    local function observe()
        local value = make_gc_value()
        collectgarbage("collect")
        local before_clear = finalized
        value = nil
        collectgarbage("collect")
        return before_clear, finalized
    end

    local before_clear, after_clear = observe()
    assert(before_clear == 0)
    assert(after_clear == 1)
    print("lua54_01_close#17", before_clear, after_clear)
end

-- lua54_01_close#18: 未读取的local call结果仍保持到作用域结束
local function test_unread_call_root_until_scope_end()
    local finalized = 0
    local function make_gc_value()
        return setmetatable({}, {
            __gc = function()
                finalized = finalized + 1
            end,
        })
    end

    local function observe()
        local old = make_gc_value()
        local values = { 1, 2, 3, 4, 5, 6, 7, 8 }
        collectgarbage("collect")
        return finalized, #values
    end

    local before, length = observe()
    assert(before == 0)
    assert(length == 8)
    print("lua54_01_close#18", before, length)
end

-- lua54_01_close#19: 不同槽的独立call不能冒充旧root的覆盖写
local function test_independent_call_does_not_overwrite_old_root()
    local finalized = 0
    local function make_gc_value()
        return setmetatable({}, {
            __gc = function()
                finalized = finalized + 1
            end,
        })
    end
    local function replacement()
        return "replacement"
    end

    local function observe()
        local old = make_gc_value()
        assert(old ~= nil)
        local table_value = {}
        local current = replacement()
        table_value.field = current
        collectgarbage("collect")
        local before_clear = finalized
        old = nil
        collectgarbage("collect")
        return before_clear, finalized, table_value.field
    end

    local before_clear, after_clear, field = observe()
    assert(before_clear == 0)
    assert(after_clear == 1)
    assert(field == "replacement")
    print("lua54_01_close#19", before_clear, after_clear, field)
end

-- lua54_01_close#20: 非紧邻MOVE不能把旧root的覆盖提前到call
local function test_delayed_move_does_not_overwrite_at_call()
    local finalized = 0
    local function make_gc_value()
        return setmetatable({}, {
            __gc = function()
                finalized = finalized + 1
            end,
        })
    end
    local function replacement()
        return "replacement"
    end

    local function observe()
        local old = make_gc_value()
        assert(old ~= nil)
        local current = replacement()
        collectgarbage("collect")
        local before_overwrite = finalized
        old = current
        collectgarbage("collect")
        return before_overwrite, finalized, old
    end

    local before_overwrite, after_overwrite, value = observe()
    assert(before_overwrite == 0)
    assert(after_overwrite == 1)
    assert(value == "replacement")
    print("lua54_01_close#20", before_overwrite, after_overwrite, value)
end

test_tbc_basic()
test_tbc_multi_exit()
test_tbc_goto_reenter()
test_close_tailcall()
test_for_const_close()
test_tbc_param_binding()
test_param_alias_gc_root()
test_table_seed_overwrite_order()
test_constructor_producer_overwrite_order()
test_nil_array_hole_length()
test_runtime_nil_array_hole()
test_integer_write_order()
test_constructor_producer_root_lifetime()
test_constructor_independent_producer_root()
test_fixed_setlist_combined_nil_shape()
test_constructor_alias_root_lifetime()
test_unused_call_result_root_lifetime()
test_unread_call_root_until_scope_end()
test_independent_call_does_not_overwrite_old_root()
test_delayed_move_does_not_overwrite_at_call()
