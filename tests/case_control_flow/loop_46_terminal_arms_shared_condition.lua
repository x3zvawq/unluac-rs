-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]

-- 两个非线性 return 臂没有共同的循环 continuation，仍须留在原循环内。
local function terminal_arms(a, b, mode)
    local n = 0
    while true do
        repeat n = n + 1 until n % 2 == 0
        if n > 2 then return "done" end
        if a or b then
            if mode == 1 then
                if a then print("first-a") else print("first-b") end
                return "first"
            elseif mode == 2 then
                if b then print("second-b") else print("second-a") end
                return "second"
            end
        end
    end
end

local function probe(label, value)
    print(label, value)
    return value
end

-- 短路条件的共享节点处于循环正文，公共尾部更新不能变成多入口 island。
local function shared_condition(a, b, c, mode)
    local n = 0
    while true do
        repeat n = n + 1 until n % 2 == 0
        if n > 2 then return "done", n end
        if probe("left", a) and probe("right", b) or c or mode == 0 then
            print("body", n)
            if mode == 1 then
                if a then print("first-a") else print("first-b") end
                return "first", n
            elseif mode == 2 then
                if b then print("second-b") else print("second-a") end
                return "second", n
            end
        end
        print("tail", n)
        n = n + 10
    end
end

for bits = 0, 7 do
    local a, b, c = bits % 2 == 1, math.floor(bits / 2) % 2 == 1, bits >= 4
    for mode = 0, 2 do
        print("terminal", bits, mode, terminal_arms(a, b, mode))
        print("shared", bits, mode, shared_condition(a, b, c, mode))
    end
end
