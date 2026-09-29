-- 连续调用结果域在同槽 callee COPY 前结束，参数准备不能遮住外层作用域。
-- unluac: expect-ast-count [[do-block]] [[3]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[9]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[table-constructor]] [[3]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=0]]
-- unluac: expect-contains [[setmetatable({}, { __mode = "v" })]]

local function make(...)
    return { marker = (...) }
end
local function forward(...)
    return ...
end

do
    local first = make(false)
    local second = make(true)
    assert(first ~= second and first.marker == false and second.marker == true)
    print("copy-window-first", first.marker, second.marker)
end

local weak = setmetatable({}, { __mode = "v" })

do
    local first = forward(make(false))
    local second = forward(make(true))
    assert(first ~= second and first.marker == false and second.marker == true)
    print("copy-window-nested", first.marker, second.marker)
end

do
    local first = make(false)
    local second = make(true)
    assert(first ~= second and first.marker == false and second.marker == true)
    print("copy-window-last", first.marker, second.marker)
end
assert(weak[1] == nil)

assert(getmetatable(weak).__mode == "v" and next(weak) == nil)
assert(select("#", forward(false, nil, true)) == 3)
assert(select(2, forward(false, nil, true)) == nil)
assert(select(3, forward(false, nil, true)) == true)
assert(select("#", forward()) == 0)
