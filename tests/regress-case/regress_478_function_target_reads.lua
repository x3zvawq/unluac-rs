-- Function sugar must preserve target-base reads for subsequent alias elimination.
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
