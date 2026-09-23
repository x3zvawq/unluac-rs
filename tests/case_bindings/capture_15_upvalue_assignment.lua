-- 相邻上值读取与写入保留 cell 身份，后续更改来源不会改变已安装的快照。
-- unluac: expect-contains [[target = source]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]]
local source = {value = "first"}
local target = {value = "old"}
local function transfer()
    target = source
end
transfer()
assert(target == source and target.value == "first")
source = {value = "second"}
assert(target.value == "first")
transfer()
assert(target == source and target.value == "second")
print("capture_15_upvalue_assignment", "OK")
