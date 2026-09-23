-- 另一槽的 capture 不改变布尔写回；即使写回值未使用，也保留原 truthiness 检查。
-- unluac: expect-contains [[not not]]
-- unluac: expect-ast-count [[assign]] [[2]] [[@proto=1]]
-- unluac: expect-not-contains [[if ]]

local function run()
    local trapped
    local read = function(value)
        trapped = value
        return trapped
    end

    for _, dead in ipairs({ 1 }) do
        dead = nil
        local marker = 7
        if dead then
            dead = true
        else
            dead = false
        end
        print("regress342-distinct-capture-home", marker)
    end

    return read
end

assert(run()(9) == 9)
