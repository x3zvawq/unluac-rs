-- 已返回分支中的引用捕获不能让另一条路径的返回常量变成 cell 写入。
-- unluac: expect-contains [[return "skip"]]
-- unluac: expect-ast-count [[do-block]] [[0]]
-- vararg 保持 Luau O2 的独立调用边界，让两条路径在同一函数中接受检查。
local function choose(flag, ...)
    if flag then
        local value = 10
        if flag == 1 then
            value = 20
        end
        local read = function(delta)
            value = value + delta
            return value
        end
        return read
    end
    return "skip"
end

local first = choose(true)
assert(choose(false) == "skip" and choose(nil) == "skip")
local second = choose(1)
assert(first(2) == 12 and second(5) == 25 and first(3) == 15)
print("terminal-capture-fallthrough", choose(false), first(1), second(2))
