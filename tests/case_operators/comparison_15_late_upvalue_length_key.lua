-- 动态键的一元操作先读旧表，再由原 GETUPVAL 读取回调替换后的表。
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=5]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=6]]
local row
local trace = {}
local function prepare(fail_length)
    trace = {}
    row = setmetatable({}, {
        __len = function()
            trace[#trace + 1] = "len"
            row = setmetatable({}, {
                __index = function(_, key)
                    trace[#trace + 1] = "index:" .. key
                    return "picked:" .. key
                end,
            })
            if fail_length then error("length failed") end
            return 7
        end,
        __index = function()
            error("indexed the old table")
        end,
    })
end

local function literal_check()
    assert(row[#row] == "picked:7", table.concat(trace, ","))
end
local function concat_check(value)
    assert(row[#row] == "picked:" .. value, table.concat(trace, ","))
end

prepare(false)
assert(select("#", literal_check()) == 0)
assert(table.concat(trace, ",") == "len,index:7")
print("literal-key-order", table.concat(trace, ","))
prepare(false)
assert(select("#", concat_check(7)) == 0)
assert(table.concat(trace, ",") == "len,index:7")
print("concat-key-order", table.concat(trace, ","))
prepare(false)
concat_check(setmetatable({}, {
    __concat = function(prefix)
        trace[#trace + 1] = "concat"
        return prefix .. "7"
    end,
}))
assert(table.concat(trace, ",") == "len,index:7,concat")
print("concat-callback-order", table.concat(trace, ","))
prepare(true)
assert(not pcall(literal_check))
assert(table.concat(trace, ",") == "len")
print("throwing-key-order", table.concat(trace, ","))
