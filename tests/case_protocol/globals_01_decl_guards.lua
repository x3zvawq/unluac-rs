-- global-decl-pretty must preserve seed order/identity/lifetime and lexical global gates.
-- unluac: expect-order [[global y =]] [[global x =]]
-- unluac: expect-contains [[global<const> print, parent_visible]]
-- unluac: expect-contains [[global<const> field_owner, print]]
-- unluac: expect-contains [[function field_owner.read]]
-- unluac: expect-not-contains [[global function field_owner.read]]
-- unluac: expect-ast-count [[function]] [[23]]
-- unluac: expect-ast-count [[close-binding]] [[1]]
-- 原零值准备由完整 global 帧重发，不能继承前一个表分配的中转绑定。
-- unluac: expect-contains [[global field_gate = 0]]
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=8]]
-- 保留 writes/env/first/second 四个原声明，尾调用不能另生 callee/argument 中转。
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=1]]
-- unluac: expect-contains [[local r1_2, r1_3 = 11, 22]]
-- unluac: expect-contains [[return table.concat(r1_0, ",")]]

local function test_write_order()
    local writes = {}
    local env = _ENV
    setmetatable(env, {
        __newindex = function(_, name)
            writes[#writes + 1] = name
        end,
    })

    local first = 11
    local second = 22
    global y = second
    global x = first
    global<const> assert, setmetatable, table

    setmetatable(env, nil)
    assert(table.concat(writes, ",") == "y,x")
    return table.concat(writes, ",")
end

local function test_captured_seed()
    local owner = 37
    local exported = function()
        return owner
    end
    global exported_closure = exported
    global<const> assert

    assert(exported_closure() == 37)
    return exported_closure()
end

local function test_physical_root()
    local weak = setmetatable({}, { __mode = "v" })
    local function remember(value)
        weak[1] = value
        return value
    end

    local rooted = remember({ marker = 41 })
    global held = rooted
    global<const> assert, collectgarbage

    held = nil
    collectgarbage("collect")
    assert(weak[1] ~= nil)
    return weak[1].marker
end

local function test_child_gate(flag)
    global gate_seed = 0
    global parent_visible
    global<const> print

    if flag then
        global parent_visible = 43
    end
    print("regress335-child", parent_visible)
    return parent_visible
end

local function test_field_root()
    local env = _ENV
    env.field_owner = { value = 47 }

    global field_gate = 0
    global field_owner
    global<const> print

    function field_owner.read()
        return field_owner.value
    end
    print("regress335-field", field_owner.read())
    return field_owner.read()
end

local function test_function_name_seed()
    local seed = {}
    global exported_seed = seed
    global<const> assert

    function seed.field()
        return 23
    end
    assert(exported_seed.field() == 23)
    return exported_seed.field()
end

local function test_nonterminal_collective()
    global gate = 0
    global<const> math, print
    local function inner()
        local value = math.max(3, 5)
        print("regress335-collective", value)
        local tail = 6
        return tail
    end
    return inner()
end

local function test_collective_lifetime()
    local force_collect = collectgarbage
    local make_weak = setmetatable
    local check = assert
    local weak = make_weak({}, { __mode = "v" })
    local function remember(value)
        weak[1] = value
        return value
    end

    global lifetime_gate = 0
    global<const> math
    local function inner()
        local rooted = remember({ marker = math.max(7, 11) })
        local marker = rooted.marker
        force_collect("collect")
        check(weak[1] ~= nil)
        return marker
    end
    return inner()
end

local function test_collective_close()
    local events = {}
    local check = assert
    local function make_close(value)
        return setmetatable({ value = value }, {
            __close = function()
                events[#events + 1] = value
            end,
        })
    end

    global close_gate = 0
    global<const> math
    local function inner()
        local item <close> = make_close(math.max(13, 17))
        local value = item.value
        check(#events == 0)
        return value
    end
    local value = inner()
    check(#events == 1 and events[1] == value)
    return value
end

local function test_collective_goto()
    global goto_gate = 0
    global<const> math, print

    local function safe_jump()
        local value = math.max(19, 23)
        goto finish
        ::finish::
        return value
    end

    local function guarded_jump(skip)
        if skip then
            goto finish
        end
        print("regress335-goto", math.max(29, 31))
        ::finish::
        return 31
    end

    return safe_jump() + guarded_jump(true) + guarded_jump(false)
end

local order = test_write_order()
local captured = test_captured_seed()
local rooted = test_physical_root()
assert(test_child_gate(false) == nil)
do
    global gate_seed
    gate_seed = nil
end
local child = test_child_gate(true)
local field = test_field_root()
local function_name_seed = test_function_name_seed()
local collective = test_nonterminal_collective()
local collective_root = test_collective_lifetime()
local collective_close = test_collective_close()
local collective_goto = test_collective_goto()
assert(order == "y,x" and captured == 37 and rooted == 41)
assert(child == 43 and field == 47 and function_name_seed == 23 and field_gate == 0)
assert(collective == 6 and collective_root == 11 and collective_close == 17)
assert(collective_goto == 85)
print(
    "regress335",
    order,
    captured,
    rooted,
    child,
    field,
    function_name_seed,
    collective,
    collective_root,
    collective_close,
    collective_goto
)
