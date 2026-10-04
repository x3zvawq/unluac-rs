-- regress_365_constructor_fields_other_return: folding constructor fields does not delete or rewrite an unrelated return
-- unluac: expect-contains [[.get()]]
-- unluac: expect-ast-count [[table-constructor]] [[3]]
-- unluac: expect-ast-count [[function]] [[4]]
-- unluac: expect-ast-max [[local-binding]] [[5]] [[@proto=0]]
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=1]]
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=3]]
-- Preserve the return identity whether allocation permits field folding or requires a write.

local function build(returned)
    local constructor = {}
    constructor.get = function()
        return 7
    end
    return returned
end

local marker = {}
assert(build(marker) == marker)

local function build_multi(returned)
    local constructor = {}
    constructor.get = function()
        return 9
    end
    return returned, constructor
end

local returned, constructor = build_multi(marker)
assert(returned == marker and constructor.get() == 9)

-- 保持构造器安装后立即返回的原路径，调用方另观察 false、nil 和结果宽度。
assert(build(false) == false)
assert(select("#", build(nil)) == 1)
assert(select("#", build_multi(nil)) == 2)
