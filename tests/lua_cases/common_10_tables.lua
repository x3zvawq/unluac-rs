-- common_10_tables#1: 表构造器与索引
local function test_ctor_index()
    local t = {
        1,
        2,
        3,
        label = "box",
        extra = 8,
    }

    t[2] = t[1] + t[3]

    print("common_10_tables#1", t[1], t[2], t[3], t.label, t.extra)
end

-- common_10_tables#2: 元表__index
local function test_metatable()
    local t = setmetatable({
        present = "yes",
    }, {
        __index = function(_, key)
            return "miss:" .. key
        end,
    })

    print("common_10_tables#2", t.present, t.absent, t.other)
end

-- common_10_tables#3: 深层嵌套构造器
local function test_deep_ctor()
    local t = {
        root = {
            nodes = {
                {
                    id = "a",
                    values = { 1, 2 },
                },
                {
                    id = "b",
                    values = { 3, 4 },
                },
            },
            flags = {
                open = true,
                closed = false,
            },
        },
    }

    t.root.nodes[2].values[1] = t.root.nodes[1].values[2] + 5

    print("common_10_tables#3", t.root.nodes[1].id, t.root.nodes[2].values[1], t.root.flags.open, #t.root.nodes)
end

-- common_10_tables#4: 深层查找与覆写
local function test_deep_lookup()
    local keys = { "left", "right" }
    local t = {
        branches = {
            left = {
                score = 4,
            },
            right = {
                score = 9,
            },
        },
    }

    local selected = t.branches[keys[2]]
    selected.score = selected.score + t.branches[keys[1]].score
    t.branches[keys[1]].score = selected.score - 3

    print("common_10_tables#4", t.branches.left.score, t.branches.right.score, selected == t.branches.right)
end

-- common_10_tables#5: 表压力测试
local function test_stress()
    local function table_stress()
        local t = {
            [1] = "hex",
            key = {
                inner = 42,
            },
            1,
            2,
            3,
        }

        t[1] = t.key.inner + t[2] + #t

        local nested_call = string.upper(string.sub(t[1] .. "hello", 1, 5))
        return t, nested_call
    end

    local t, nested_call = table_stress()
    print("common_10_tables#5", t[1], t[2], t[3], t.key.inner, nested_call)
end

-- common_10_tables#6: 复杂初始化模式
local function test_crazy_init()
    local function crazy_table_init()
        local t = {
            1,
            2,
            3,
            a = 4,
            [5] = 6,
            7,
            8,
            f = function()
                return 9
            end,
            string.byte("A"),
        }

        return t
    end

    local t = crazy_table_init()
    print("common_10_tables#6", t[1], t[2], t[3], t[4], t[5], t[6], t.a, t.f())
end

-- common_10_tables#7: 嵌套表调用索引
local function test_nested_call()
    local function build(seed)
        return {
            branch = {
                [seed] = function(x)
                    return seed + x
                end,
            },
            pick = function(self, key)
                return self.branch[key]
            end,
        }
    end

    local obj = build(4)
    local fn = obj:pick(4)

    print("common_10_tables#7", fn(8), obj.branch[4](2))
end

-- common_10_tables#8: 动态深层覆写
local function test_dynamic_overwrite()
    local suffix = "tail"
    local key = "slot_" .. suffix

    local t = {
        list = {
            10,
            20,
            30,
        },
        meta = {
            [key] = 7,
        },
    }

    t.list[2] = t.list[1] + t.meta[key]
    t.meta[key] = t.list[3] - t.list[2]

    print("common_10_tables#8", t.list[1], t.list[2], t.list[3], t.meta[key], t.meta.slot_tail)
end

-- common_10_tables#9: 构造器与函数混合
local function test_ctor_function_mix()
    local function build(seed)
        return {
            seed = seed,
            steps = {
                function(x)
                    return seed + x
                end,
                function(x)
                    return seed * x
                end,
            },
            call = function(self, index, value)
                return self.steps[index](value)
            end,
        }
    end

    local obj = build(6)
    print("common_10_tables#9", obj:call(1, 4), obj:call(2, 3), obj.steps[1](1))
end

test_ctor_index()
test_metatable()
test_deep_ctor()
test_deep_lookup()
test_stress()
test_crazy_init()
test_nested_call()
test_dynamic_overwrite()
test_ctor_function_mix()
