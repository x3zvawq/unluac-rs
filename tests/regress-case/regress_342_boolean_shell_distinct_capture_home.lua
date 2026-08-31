-- A reference-captured local in another slot does not observe the dead loop-local shell.
-- unluac: expect-not-contains [[not not]]
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
