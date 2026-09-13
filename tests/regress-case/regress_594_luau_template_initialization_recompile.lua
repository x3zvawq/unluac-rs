-- Luau DUPTABLE 的隐式数值 0 与原显式字段初始化不能每轮各输出一次。
-- 重复真实字段写及回调观察仍保留；由三轮源码/字节码再生检查稳定性。
local function repeated_zero()
    local value = { __mode = 0 }
    local key = "__mode"
    value[key] = "v"
    return value.__mode
end

local function ordered_fields()
    local trace = ""
    local function mark(label, value)
        trace = trace .. label
        return value
    end
    local value = { a = mark("a", 0), b = mark("b", 2), a = mark("c", 3) }
    assert(trace == "abc", "real duplicate field evaluations were reordered")
    assert(value.a == 3 and value.b == 2)
    return trace
end

local function visible_initialization()
    local value = { a = 0, b = 0 }
    local function observe()
        assert(value.a == 0 and value.b == 0, "template state changed before its observer")
        return 7
    end
    value.b = observe()
    value.a = 9
    return value.a + value.b
end

local function observed_resource()
    local weak = setmetatable({}, { __mode = "v" })
    local resource = {}
    weak[1] = resource
    local value = { item = resource, state = 0 }
    resource = nil
    local function observe()
        for index = 1, 20000 do
            local garbage = { index, index + 1, index + 2 }
        end
        assert(weak[1] ~= nil, "initialized field lost its strong resource")
        assert(value.item == weak[1] and value.state == 0)
        return 1
    end
    value.state = observe()
    return value.state
end

-- 两个低槽 Local 由 FASTCALL 直接读取，fallback 才 COPY 到参数区。
-- 结果后继续写低槽并捕获弱表，保证机械别名不能在每轮重编译时增加一层。
local function fastcall_argument_copies()
    local object = {}
    local meta = { __mode = "v" }
    local object_arg = object
    local meta_arg = meta
    local final_arg = meta_arg
    local weak = setmetatable(object_arg, final_arg)
    object = {}
    weak[1] = object
    meta_arg = function() return weak[1] end
    final_arg = meta_arg
    return final_arg() == object
end

-- 开放参数保留全部返回值，不压成一个 Boolean。
local function open_assert(factory)
    assert(factory())
end
local function open_values()
    return true, "tail", 3
end
open_assert(open_values)

assert(repeated_zero() == "v")
assert(ordered_fields() == "abc")
assert(visible_initialization() == 16)
assert(observed_resource() == 1)
assert(fastcall_argument_copies())
-- getfenv 将当前环境标为不安全；再次调用覆盖同一字节码的 fallback 路径。
getfenv(0)
open_assert(open_values)
assert(fastcall_argument_copies())
print("regress_594_luau_template_initialization_recompile", "ok")
