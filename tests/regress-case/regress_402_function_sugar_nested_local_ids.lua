-- regress_402_function_sugar_nested_local_ids: child LocalIds do not count as outer chain uses
-- unluac: expect-contains [[:begin():finish(function()]]

local function build(obj)
    local value = obj:begin()
    value:finish(function()
        local value = side()
        use(value)
        return value
    end)
end

return build
