if ... == "--dump-table-remove" then
    io.stdout:write(string.dump(table.remove, true))
    return
end

local function probe(remove)
    local values = { "a", "b", "c", "d" }
    rawset(values, 2, nil)

    local reads = 0
    local writes = 0
    setmetatable(values, {
        __index = function(_, key)
            reads = reads + 1
            return "meta" .. key
        end,
        __newindex = function(table_value, key, value)
            writes = writes + 1
            rawset(table_value, key, value)
        end,
    })

    local size = #values
    local removed = remove(values, 1)
    return size, removed, rawget(values, 1), rawget(values, 2), rawget(values, 3),
        rawget(values, 4), reads, writes
end

local function indexed_remove(values, position)
    local size = #values
    local removed = values[position]
    for index = position, size - 1 do
        values[index] = values[index + 1]
    end
    values[size] = nil
    return removed
end

-- luajit_02_ljlib_table_remove#1: LJLIB_LUA table.remove 必须绕过 __index/__newindex。
local size, removed, value1, value2, value3, value4, reads, writes = probe(table.remove)
assert(size == 4 and removed == "a")
assert(value1 == nil and value2 == "c" and value3 == "d" and value4 == nil)
assert(reads == 0 and writes == 0)
print("luajit_02_ljlib_table_remove#1", size, removed, value1, value2, value3, value4,
    reads, writes)

-- luajit_02_ljlib_table_remove#2: 普通索引实现可观察地触发元方法，不能替代 raw opcode。
size, removed, value1, value2, value3, value4, reads, writes = probe(indexed_remove)
assert(size == 4 and removed == "a")
assert(value1 == "meta2" and value2 == "c" and value3 == "d" and value4 == nil)
assert(reads == 1 and writes == 1)
print("luajit_02_ljlib_table_remove#2", size, removed, value1, value2, value3, value4,
    reads, writes)
