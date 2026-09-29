-- regress_169_same_header_conditional_sibling_latch#1: 内层分支退出整个循环时不能误拆 same-header latch
-- unluac: expect-contains [[while true do]]
-- unluac: expect-not-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b)
    local x = 0
    while true do
        if a then
            if b then
                break
            end
        else
            x = x + 1
        end
    end
    return x
end

local result = run(true, true)
assert(result == 0)
print("regress_169_same_header_conditional_sibling_latch#1", result)

local dispatch = {run}
assert(dispatch[1](0, 0) == 0)
assert(dispatch[1]("", true) == 0)
-- PUC 的指令 hook 有界执行无出口分支，不要求不同字节码的指令计数相同。
local stop = {}
local function interrupt_loop()
    debug.sethook()
    error(stop)
end
local cases = {{false, true}, {true, false}, {nil, nil}}
for i = 1, #cases do
    debug.sethook(interrupt_loop, "", 1000)
    local ok, failure = pcall(dispatch[1], cases[i][1], cases[i][2])
    debug.sethook()
    assert(not ok and failure == stop)
end
print("observed_nonterminal_paths", #cases)
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]]
