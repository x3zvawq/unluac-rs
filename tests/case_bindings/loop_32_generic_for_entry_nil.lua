-- 入口已有 nil 的低槽声明先于 iterator 准备，不插在 CALL 与循环头之间。
-- unluac: expect-not-contains [[= ipairs]]
-- unluac: expect-ast-max [[local-binding]] [[4]]
local function run()
    local result
    for key, value in ipairs({ 1, 2 }) do
        result = key + value
    end
    return result
end

assert(run() == 4)
print("generic-for-entry-nil", run())
