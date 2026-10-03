-- 固定变参声明与返回准备 COPY 分属两次写入，源码只保留一组接收变量。
-- unluac: expect-ast-max [[local-binding]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
local function first_two(...)
    local first, second = ...
    return first, second
end
local token = {}
local first, second, extra = first_two(token, nil, false)
assert(first == token and second == nil and extra == nil)
assert(select("#", first_two(token, nil, false)) == 2)
assert(select("#", first_two()) == 2)
first, second = first_two()
assert(first == nil and second == nil)
first, second = first_two(false, 7, 8)
assert(first == false and second == 7)
print(select("#", first_two()), first, second)
