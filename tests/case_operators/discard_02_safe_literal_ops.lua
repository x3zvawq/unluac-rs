-- unluac: expect-not-contains [[11 + 7]]
-- unluac: expect-not-contains [[-(13 * 5)]]
-- unluac: expect-not-contains [[29 / 3]]
-- unluac: expect-not-contains [[2 ^ 8]]
-- unluac: expect-not-contains [[#"literal-length"]]

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

discard_add()
discard_nested_negation()
discard_division()
discard_power()
discard_string_length()
assert(not pcall(reject_number_length))
assert(not pcall(reject_mixed_ordering))
