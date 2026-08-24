-- common_14_loop_lexical_arms#1: while 正文的纯 return arm 保持在词法循环内
local function test_return_arm()
    local function run(flag)
        local turns = 0
        while turns < 3 do
            turns = turns + 1
            if flag then
                return turns
            end
        end
        return turns
    end

    print("common_14_loop_lexical_arms#1", run(true), run(false))
end

-- common_14_loop_lexical_arms#2: while 后的闭合循环不能被收进前一个 loop body
local function test_closed_sibling()
    local function run(enter)
        local turns = 0
        while enter do
            turns = turns + 1
            enter = false
        end
        while true do
            if turns >= 0 then
                return turns
            end
        end
    end

    print("common_14_loop_lexical_arms#2", run(true), run(false))
end

test_return_arm()
test_closed_sibling()
