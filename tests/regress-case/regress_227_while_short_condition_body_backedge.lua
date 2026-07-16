-- regress_227_while_short_condition_body_backedge#1: while body 不能冒充 repeat 回边 pad
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c)
    local count = 0
    while (a or b) and c do
        count = count + 1
        a = false
        b = false
    end
    return count
end

print(run(true, false, true), run(false, true, true), run(true, true, false))
