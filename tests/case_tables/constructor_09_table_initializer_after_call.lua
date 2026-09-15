-- 前一 CALL 用过的槽仍是新声明的分配目标；record value/key 的同槽复用不能拆散原 initializer。
-- unluac: expect-ast-count [[table-constructor]] [[4]]
-- unluac: expect-ast-count [[table-list-field]] [[3]]
-- unluac: expect-ast-count [[table-record-field]] [[3]]
print("regress_646")
local rows = { { 1 }, key = { value = 3 }, [{ 2 }] = 3 }
assert(rows[1][1] == 1 and rows.key.value == 3)
local keys = 0
for key, value in pairs(rows) do
    if type(key) == "table" then
        assert(key[1] == 2 and value == 3)
        keys = keys + 1
    end
end
assert(keys == 1)
