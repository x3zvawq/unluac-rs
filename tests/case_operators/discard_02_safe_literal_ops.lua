-- unluac: expect-ast-count [[function]] [[8]]
-- unluac: expect-ast-count [[if]] [[7]]
-- unluac: expect-ast-max [[local-binding]] [[16]]
-- 无观察事件不等于没有原操作；包括永不到达的分支关系也保留。
-- unluac: expect-contains [[11 + 7]]
-- unluac: expect-contains [[-(13 * 5)]]
-- unluac: expect-contains [[29 / 3]]
-- unluac: expect-contains [[2 ^ 8]]
-- unluac: expect-contains [[#"literal-length"]]
-- unluac: expect-count [[if 1 == 1 then]] [[7]]

local function discard_add()
    local left = 11
    local right = 7
    local unused = left + right
    if 1 == 1 then
        print("discard-add")
    else
        print("unreachable", unused)
    end
end

local function discard_nested_negation()
    local left = 13
    local right = 5
    local product = left * right
    local unused = -product
    if 1 == 1 then
        print("discard-nested-negation")
    else
        print("unreachable", unused)
    end
end

local function discard_division()
    local numerator = 29
    local denominator = 3
    local unused = numerator / denominator
    if 1 == 1 then
        print("discard-division")
    else
        print("unreachable", unused)
    end
end

local function discard_power()
    local base = 2
    local exponent = 8
    local unused = base ^ exponent
    if 1 == 1 then
        print("discard-power")
    else
        print("unreachable", unused)
    end
end

local function discard_string_length()
    local value = "literal-length"
    local unused = #value
    if 1 == 1 then
        print("discard-string-length")
    else
        print("unreachable", unused)
    end
end

local function reject_number_length()
    local value = 1
    local unused = #value
    if 1 == 1 then
        print("unreachable-after-number-length")
    else
        print(unused)
    end
end

local function reject_mixed_ordering()
    local left = 1
    local right = "one"
    local unused = left < right
    if 1 == 1 then
        print("unreachable-after-mixed-ordering")
    else
        print(unused)
    end
end

local original_print = print
local calls = 0
print = function(label, ...)
    calls = calls + 1
    assert(type(label) == "string" and string.sub(label, 1, 8) == "discard-")
    assert(select("#", ...) == 0)
    original_print(label)
end

discard_add()
discard_nested_negation()
discard_division()
discard_power()
discard_string_length()
assert(not pcall(reject_number_length))
assert(not pcall(reject_mixed_ordering))

assert(calls == 5)
assert(select("#", discard_add()) == 0)
assert(select("#", discard_nested_negation()) == 0)
assert(select("#", discard_division()) == 0)
assert(select("#", discard_power()) == 0)
assert(select("#", discard_string_length()) == 0)
assert(calls == 10)
assert(select("#", pcall(reject_number_length)) == 2)
assert(select("#", pcall(reject_mixed_ordering)) == 2)
assert(calls == 10)
print = original_print
assert(print == original_print)
