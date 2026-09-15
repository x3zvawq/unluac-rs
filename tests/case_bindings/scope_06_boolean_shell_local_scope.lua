-- A boolean shell must not move a local declaration after the condition evaluation.

local function caller_has_local(expected)
    for index = 1, 64 do
        local name = debug.getlocal(2, index)
        if name == expected then
            return true
        end
    end
    return false
end

local function run()
    local result
    if caller_has_local("result") then
        result = true
    else
        result = false
    end
    return result
end

assert(run() == true)
print("regress342", run())
