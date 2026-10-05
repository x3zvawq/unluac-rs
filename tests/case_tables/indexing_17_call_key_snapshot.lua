-- CALL 键在原算术 scratch 求值；改写同名上值不能改变各方言原生的目标读取时点。
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]] [[@dialect=luau]]
local original = {}
local replacement = {}
local target = original
local calls = 0
local function select_key()
    calls = calls + 1
    target = replacement
    return 0, "discarded"
end
local function write(index)
    target[select_key() + index] = "value"
end
write(2)
assert(target == replacement and calls == 1)
assert((original[2] == "value") ~= (replacement[2] == "value"))
-- SETTABUP/后读 GETUPVAL 与先快照目标的 VM 布局不同；实际写入哪张表参与运行比较。
print("call key snapshot", original[2], replacement[2], calls)
