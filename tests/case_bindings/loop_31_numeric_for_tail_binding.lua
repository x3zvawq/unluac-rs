-- numeric-for 的尾部普通语句仍读取本轮可写 binding，不另建分支出口副本。
-- unluac: expect-ast-max [[local-binding]] [[3]]
-- unluac: expect-not-contains [[ = nil]]
local function run(flag)
    local total = 0
    for index = 1, 2 do
        if flag then
            index = index + 10
        else
            index = index + 20
        end
        total = total + index
    end
    return total
end

assert(run(true) == 23)
assert(run(false) == 43)
print("numeric-for-tail-binding", run(true), run(false))
