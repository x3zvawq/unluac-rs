-- regress_135_same_header_sibling_latches#1: 单个循环的 sibling latch 不能误拆成嵌套 loop
-- unluac: expect-contains [[while true do]]
-- unluac: expect-not-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
local function run(a, c)
    local x = 0
    while true do
        if a then
            if c then
                break
            end
            x = x + 1
        else
            x = x + 10
        end
    end
    return x
end

print("regress_135_same_header_sibling_latches#1", run(true, true))
