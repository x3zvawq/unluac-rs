-- regress_402_method_alias_nested_write_ids: child direct writes do not target an outer same-numbered alias
-- unluac: expect-contains [[:m()]]

local function run(obj)
    local receiver = obj
    receiver.m(receiver)

    local function later()
        local receiver
        if flag then
            receiver = side()
        else
            receiver = other()
        end
        use(receiver)
        return receiver
    end

    return later
end

return run
