-- 低槽查表声明须保留到高槽算术初始化；元方法观察后续读取、写入与异常边界。
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=5]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=5]]
-- unluac: expect-ast-count [[call]] [[0]] [[@proto=5]]
local events = {}
local stop = false
local current_seed
local stored = -1
local left, shifted, seed, shifted_seed, merged, combined = {}, {}, {}, {}, {}, {}
local function method(name, expected_left, expected_right, result)
    return function(a, b)
        assert(a == expected_left and b == expected_right)
        events[#events + 1] = name
        if name == "shl" then
            if stop then
                error("shift-stop")
            end
            current_seed = seed
        end
        return result
    end
end
setmetatable(left, { __shl = method("shl", left, 2, shifted) })
setmetatable(seed, { __shr = method("shr", seed, 1, shifted_seed) })
setmetatable(shifted, { __bor = method("or", shifted, shifted_seed, merged) })
setmetatable(merged, { __bxor = method("xor", merged, 6, combined) })
setmetatable(combined, {
    __band = method("and", combined, 255, 77),
    __idiv = method("floor", combined, 3, 25),
})
local source = setmetatable({}, {
    __index = function(_, key)
        if key == 1 then
            events[#events + 1] = "read"
            return left
        elseif key == "seed" then
            events[#events + 1] = "seed"
            assert(current_seed == seed)
            return current_seed
        else
            assert(key == 2)
            events[#events + 1] = "result"
            return stored
        end
    end,
    __newindex = function(_, key, value)
        assert(key == 2 and value == 77)
        events[#events + 1] = "write"
        stored = value
    end,
})
local function combine(input, shift)
    local base = input[1]
    local result = ((base << shift) | (input.seed >> (shift - 1))) ~ (shift * 3)
    input[2] = result & 255
    return input[2], result // 3
end
local a, b, extra = combine(source, 2)
assert(a == 77 and b == 25 and extra == nil and stored == 77)
assert(table.concat(events, ",") == "read,shl,seed,shr,or,xor,and,write,result,floor")
events = {}
current_seed = nil
assert(select("#", combine(source, 2)) == 2)
assert(table.concat(events, ",") == "read,shl,seed,shr,or,xor,and,write,result,floor")
events = {}
current_seed = nil
stop = true
local ok, message = pcall(combine, source, 2)
assert(not ok and string.find(message, "shift%-stop"))
assert(table.concat(events, ",") == "read,shl")
assert(stored == 77 and current_seed == nil)
print("prepared-integer-metamethods", "OK")
