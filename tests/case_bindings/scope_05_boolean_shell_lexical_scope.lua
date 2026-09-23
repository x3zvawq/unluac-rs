-- A boolean shell must not move a local declaration across an initializer that reads it.
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]]

local result = true

local function run()
    local result
    if (function()
        return result
    end)() then
        result = true
    else
        result = false
    end
    return result
end

assert(run() == false)
print("regress342-lexical", run())
