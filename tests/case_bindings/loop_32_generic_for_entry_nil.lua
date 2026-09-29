-- 入口已有 nil 的低槽声明先于 iterator 准备，不插在 CALL 与循环头之间。
-- unluac: expect-not-contains [[= ipairs]]
-- unluac: expect-ast-count [[local-binding]] [[4]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=1]]
local function run(stop)
    local result
    for key, value in ipairs({ 1, 2 }) do
        if stop then
            break
        end
        result = key + value
    end
    return result
end

assert(run() == 4)
assert(run(true) == nil)
print("generic-for-entry-nil", run())
