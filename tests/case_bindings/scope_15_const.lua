-- lua54_02_const#1: const局部变量
local function test_const_local()
    local answer <const> = 42

    local function read_answer()
        return answer
    end

    print("lua54_02_const#1", read_answer(), answer)
end

-- lua54_02_const#2: const闭包交叉
local function test_const_closure()
    local function make_pipeline(seed)
        local bias <const> = seed * 3
        local prefix <const> = "p" .. seed

        local function stage_one(value)
            local adjust <const> = bias + value
            return function(flag)
                if flag then
                    return prefix .. ":" .. (adjust + seed)
                end
                return prefix .. ":" .. (adjust - seed)
            end
        end

        return function(values)
            local out = {}
            for i = 1, #values do
                local emit = stage_one(values[i])
                out[#out + 1] = emit(i % 2 == 0)
            end
            return table.concat(out, "|")
        end
    end

    local run = make_pipeline(4)
    print("lua54_02_const#2", run({ 1, 2, 3, 4 }))

end

-- lua54_02_const#3: 变参与const管线
local function test_vararg_const()
    local function pack_sum(tag, ...)
        local prefix <const> = tag
        local values = { ... }
        local total = 0

        for i = 1, #values do
            local current <const> = values[i]
            if i % 2 == 0 then
                total = total + current * i
            else
                total = total + current
            end
        end

        return prefix .. ":" .. total, #values
    end

    local function forward(...)
        return pack_sum("sum", ...)
    end

    local first, second = forward(3, 4, 5, 6)
    print("lua54_02_const#3", first, second)

end

test_const_local()
test_const_closure()
test_vararg_const()
