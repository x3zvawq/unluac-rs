-- NEWTABLE preserves capacity even when string keys can be printed as named fields.
-- unluac: expect-ast-count [[table-constructor]] [[7]]
-- 容量要求的后续字段写保持清晰，两个开放尾直接留在构造器中。
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=1]]
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=7]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=8]]
-- unluac: expect-ast-count [[table-list-field]] [[2]] [[@proto=7]]
-- unluac: expect-ast-count [[table-list-field]] [[2]] [[@proto=8]]
local function grow(value)
    local result = { ["a"] = 1, ["b"] = nil, ["c"] = value, ["d"] = 4 }
    result.e = 5
    return result
end
for key, value in pairs(grow(7)) do
    print("growth", key, value)
end

-- Function sugar must apply the same capacity check after extending its candidate.
local function grow_function(value)
    local result = { ["a"] = 1, ["b"] = nil, ["c"] = value, ["d"] = 4 }
    result.e = function() return 5 end
    return result
end
for key, value in pairs(grow_function(7)) do
    if type(value) == "function" then value = value() end
    print("function", key, value)
end

local function numeric(value)
    return { [1] = false, a = value, [2] = true, [3] = false }
end
local result = numeric(7)
result[1] = nil
result[3] = nil
print("numeric", #result, result[2], result.a)

-- A sparse extra key cancels the compiler's explicit sequential-key allocation.
local function sparse()
    return { [1] = false, [2] = true, [3] = false, [17] = 42 }
end
local gaps = sparse()
gaps[1] = nil
gaps[3] = nil
print("sparse", #gaps, gaps[2], gaps[17])

local function many(enabled)
    if enabled then return nil, 3 end
end
local function call_tail(enabled)
    return { 9, many(enabled) }
end
local function vararg_tail(...)
    return { 9, ... }
end
for _, enabled in ipairs({ false, true }) do
    local called = call_tail(enabled)
    local varied = vararg_tail(many(enabled))
    print("tails", enabled, #called, called[1], called[2], called[3],
        #varied, varied[1], varied[2], varied[3])
end
