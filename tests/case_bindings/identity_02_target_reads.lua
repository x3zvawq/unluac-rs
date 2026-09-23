-- Function sugar must preserve target-base reads for subsequent alias elimination.
-- unluac: expect-ast-min [[function]] [[6]]
-- unluac: expect-ast-min [[method-call]] [[1]]
-- Luau must retain the shared RHS scratch of the two-target declaration and absorb call comparisons.
-- unluac: expect-count [[nested = {}]] [[2]] [[@dialect=luau]]
-- 嵌套 callee 的原同槽读取应保留为完整比较参数，不产生读取、调用和比较的声明链。
-- unluac: expect-contains [[.nested.field() == 23)]]
-- unluac: expect-ast-max [[local-decl]] [[6]] [[@proto=0]]
-- unluac: expect-contains [[.nested.field()]]
-- 三个 installer 各只保留条件选出的 alias，闭包转发不额外声明函数。
-- unluac: expect-ast-count [[local-function]] [[3]] [[@proto=0]]
-- unluac: expect-ast-count [[local-function]] [[3]]
local function install(flag, left, right)
    local alias = flag and left or right
    function alias.field()
        return 17
    end
    return alias
end

local function install_method(flag, left, right)
    local alias = flag and left or right
    function alias:method()
        return self.tag
    end
    return alias
end

local function install_nested(flag, left, right)
    local alias = flag and left or right
    function alias.nested.field()
        return 23
    end
    return alias
end

for _, flag in ipairs({true, false}) do
    local left, right = {tag = "left", nested = {}}, {tag = "right", nested = {}}
    local selected = flag and left or right
    assert(install(flag, left, right) == selected)
    assert(selected.field() == 17)
    assert(install_method(flag, left, right) == selected)
    assert(selected:method() == selected.tag)
    assert(install_nested(flag, left, right) == selected)
    assert(selected.nested.field() == 23)
end
print("function targets ok")
