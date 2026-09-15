-- regress_196_child_writes_parent_capture#1: 子 proto 写入的父级 capture 不能跨 call 常量传播
-- unluac: expect-not-contains [[false()]]
-- unluac: expect-not-contains [[nil()]]
-- unluac: expect-not-contains [[unluac error]]
local saved = false

local function install()
    saved = function()
        return 42
    end
end

install()
local saved_value = saved()
assert(saved_value == 42)
print("regress_196_child_writes_parent_capture#1", saved_value)

-- regress_196_child_writes_parent_capture#2: 后代 proto 透传写入同样必须回传 mutability
local nested_saved = false

local function factory()
    return function()
        nested_saved = function()
            return 84
        end
    end
end

local nested_install = factory()
nested_install()
local nested_value = nested_saved()
assert(nested_value == 84)
print("regress_196_child_writes_parent_capture#2", nested_value)

-- regress_196_child_writes_parent_capture#3: 入口隐式 nil 槽在 call 后仍须读取 local 身份
local empty_saved

local function install_empty()
    empty_saved = function()
        return 126
    end
end

install_empty()
local empty_value = empty_saved()
assert(empty_value == 126)
print("regress_196_child_writes_parent_capture#3", empty_value)

-- regress_196_child_writes_parent_capture#4: Close 管理的逐迭代 capture 仍须保持每轮身份
local seen = {}
for i = 1, 2 do
    local value = i
    local function bump()
        value = value + 10
    end
    bump()
    seen[i] = value
end
assert(seen[1] == 11 and seen[2] == 12)
