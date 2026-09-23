-- 分配结果写入上值后，同槽 GETUPVAL/RETURN 属于下一值版本，不保留机械 local 交接。
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=3]]
-- 调用结果、已有低槽比较与任意值短路末项共同组成原 assert 参数帧。
-- unluac: expect-count [[assert(]] [[5]]
local state = {}
local function read()
    return state
end
local function replace_empty()
    state = {}
    return read
end
local function replace_record()
    state = { value = 42, ready = true }
    return read
end

local previous = state
local selected = replace_empty()
assert(selected == read and state ~= previous)
assert(selected() == state)
local first = state
selected = replace_record()
assert(selected == read and state ~= first)
assert(selected() == state and state.value == 42 and state.ready)
selected = replace_empty()
assert(selected() == state and state ~= first and state.value == nil)
print("upvalue scratch return", previous ~= first, state ~= first)
