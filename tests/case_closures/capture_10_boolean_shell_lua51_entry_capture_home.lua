-- A Lua 5.1 implicit vararg table is an entry local with the vararg register's home.
-- unluac: expect-not-contains [[not not]]

local function run(...)
    local read = function()
        return arg
    end

    for _, dead in ipairs({ 1 }) do
        dead = nil
        local marker = 7
        if dead then
            dead = true
        else
            dead = false
        end
        print("regress342-lua51-entry-capture-home", marker)
    end

    return read
end

local pack = run(9)()
assert(pack[1] == 9 and pack.n == 1)
