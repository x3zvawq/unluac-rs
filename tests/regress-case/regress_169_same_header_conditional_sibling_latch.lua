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

print("regress_169_same_header_conditional_sibling_latch#1", run(true, true))
