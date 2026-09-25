-- 模板中的闭包占位属于初始化，真实常量字段及闭包共享的捕获 cell 都须保留。
-- unluac: expect-ast-count [[table-record-field]] [[4]]
-- unluac: expect-not-contains [[read = 0]]
-- unluac: expect-not-contains [[write = 0]]
-- unluac: expect-contains [[assert(object.enabled and object.read(1) == 5)]] [[@debug=retained]]
-- 无捕获闭包所在的表先离域，后续捕获复用同槽不能阻止原 debug initializer。
-- unluac: expect-not-contains [[f = 0]]
-- unluac: expect-not-contains [[f = nil]]
do
    local plain = { f = function() return "old" end }
    assert(plain.f() == "old")
    plain.f = function() return "new" end
    assert(plain.f() == "new")
end
local seed = 4
local reads = 0
local object = {
    read = function(delta)
        reads = reads + 1
        return seed + delta
    end,
    enabled = true,
    write = function(value) seed = value end,
}
assert(object.enabled and object.read(1) == 5)
assert(reads == 1)
object.enabled = false
print(object.enabled and object.read(2) == 6)
assert(reads == 1)
object.write(8)
assert(object.read(3) == 11)
assert(reads == 2)
print("template_07_record_closure_initializers", "OK")
