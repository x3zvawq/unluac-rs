-- 同值 incoming 只代表选择时的快照；之后改写被引用捕获的参数不能改变 chosen。
-- unluac: expect-contains [[local chosen]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=5]] [[@variant=O0]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=5]] [[@variant=O0]]
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
