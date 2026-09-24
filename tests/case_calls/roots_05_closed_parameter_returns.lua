-- 同一函数的原始值调用不能覆盖资源实参；逃逸入口也不能沿用直接调用的参数域。
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[assert(false == false)]]
-- unluac: expect-not-contains [[assert(7 == 7)]]
-- unluac: expect-ast-count [[table-list-field]] [[1]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[10]] [[@proto=0]] [[@variant=default]]
-- unluac: expect-ast-count [[local-binding]] [[10]] [[@proto=0]] [[@variant=O2]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=0]] [[@variant=O2]]
local weak = setmetatable({}, { __mode = "v" })
local observations = 0
local function make_callable()
    local value = setmetatable({}, {
        __call = function()
            for index = 1, 20000 do
                local garbage = { index, index + 1, index + 2 }
            end
            assert(weak[1] ~= nil, "callable root was released before its call")
            observations = observations + 1
            return 42
        end,
    })
    weak[1] = value
    return value
end

local function forward(value)
    return value
end
assert(forward(false) == false)
local function run_direct()
    local callable = forward(make_callable())
    return "direct", callable()
end
local label, value = run_direct()
assert(label == "direct" and value == 42)

local function exported(value)
    return value
end
assert(exported(7) == 7)
local routes = { exported }
local function run_exported()
    local callable = routes[1](make_callable())
    return "exported", callable()
end
label, value = run_exported()
assert(label == "exported" and value == 42 and observations == 2)
print("closed-parameter-roots", observations)
