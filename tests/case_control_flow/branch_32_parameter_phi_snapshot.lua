-- 同值 incoming 只代表选择时的快照；之后改写被引用捕获的参数不能改变 chosen。
-- NOT 直接作为比较 RHS；允许匿名绑定合并后重新编号。
-- unluac: expect-contains [[local chosen]] [[@debug=retained]]
-- check 只声明两个调用结果；比较 RHS 的原 NOT 应留在完整参数表达式内。
-- O2 的表输入使根函数也保留 NOT；helper 与内联调用都应直接形成比较 RHS。
-- 后续候选撤回不应阻断八个独立词法窗口中的比较参数。
local function choose(flag, returned)
    local function left()
        return returned
    end
    local function right()
        return returned
    end
    local chosen
    if flag then
        chosen = left()
    else
        chosen = right()
    end
    returned = not returned
    return chosen, returned
end

local function check(flag, value)
    local previous, current = choose(flag, value)
    assert(previous == value)
    assert(current == not value)
end
check(true, true)
check(true, false)
check(false, true)
check(false, false)
check(true, nil)
check(false, 0)
check(true, "")
check(false, {})

-- 参数本身只读也不够：MOVE 链经过引用捕获的中间 binding 时，回调能改写它。
local function capture_chain(flag, original)
    local alias = original
    local function replace()
        alias = false
    end
    replace()
    local chosen, marker
    if flag then
        marker = 1
        chosen = alias
    else
        marker = 2
        chosen = alias
    end
    return chosen, original, marker
end

local selected, original, marker = capture_chain(true, true)
assert(selected == false and original == true and marker == 1)
selected, original, marker = capture_chain(false, true)
assert(selected == false and original == true and marker == 2)
print("branch_32_parameter_phi_snapshot")
