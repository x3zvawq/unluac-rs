-- regress_115_luau_branch_mixed_entry_update_owner#1: BVM 混合 preserved/update 路径继承 state owner
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- 入口初始化与分支/循环更新共用原 state owner，不额外物化合流空声明。
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-contains [[local r1_0 = 0]]
-- Luau O2 内联调用后仍留下的 ADD 不因两侧成为常量而消失。
-- unluac: expect-contains [[0 + 1]]
local function nested(a, b, c, xs)
    local x = 0
    if a then
        repeat
            for k, v in xs do
                if c then
                    print(x)
                else
                    x = x + 1
                end
            end
        until c
        if b then
            print(x)
        else
            if a then
                x = x + 1
            end
            while not b do
                for k, v in xs do
                    x = x + 1
                end
                if c then
                    continue
                else
                    x = x + 1
                    break
                end
            end
        end
    else
        x = x + 1
    end
    return x
end

print("regress_115_luau_branch_mixed_entry_update_owner#1", nested(true, true, true, {}))
assert(nested(false, false, false, {}) == 1)
assert(nested(true, true, true, {10, 20}) == 0)
