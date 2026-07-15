-- unluac: expect-contains [[missing_global]]

local env = _VERSION == "Lua 5.1" and getfenv() or _ENV
local global_hits = 0

setmetatable(env, {
    __index = function(_, key)
        if key == "missing_global" or key == "probe" then
            global_hits = global_hits + 1
            return true
        end
    end,
})

local unused = missing_global
print("global-read", global_hits)

global_hits = 0
local global_value = (probe and false) or (probe and true)
print("global-logic", global_hits, global_value)

local compare_hits = 0
local mt = {
    __lt = function()
        compare_hits = compare_hits + 1
        return true
    end,
}
local left, right = setmetatable({}, mt), setmetatable({}, mt)
local compare_value = (left < right and false) or (left < right and true)
print("metamethod-logic", compare_hits, compare_value)

local function shared_rhs(a, b, c)
    return (a and b) or (c and b)
end

local function reordered_or(c, a, b)
    return c or (a and (b or c))
end

print(
    "logical-value",
    shared_rhs(true, nil, false) == false,
    reordered_or("first", true, "later")
)
