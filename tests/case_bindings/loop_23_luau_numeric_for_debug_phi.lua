-- numeric-for 的语法 binding 已提供本轮 phi 值；原 SETLIST buffer COPY 仍须保留。
-- unluac: expect-ast-min [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[numeric-for]] [[2]]
-- retain-debug 再编译不能每轮新建一个 local index2 = index。
local total = 0
for index = 1, 3 do
    local garbage = { index, index + 1, index + 2 }
    total = total + garbage[1]
end
assert(total == 6)

-- 真实 body 写和前值快照仍是不同动作，不能把所有同 home phi copy 都删除。
local count = 0
local feedback = 0
for index = 1, 3 do
    local before = index
    index = index + 10
    count = count + 1
    feedback = feedback + index - before
end
assert(feedback == count * 10)
print("regress_595_luau_numeric_for_debug_phi", total, count, feedback)
