-- Cleanup ownership must preserve both goto exits and the later sibling's lifetime.
-- unluac: expect-contains [[<close>]]
-- unluac: expect-ast-count [[close-binding]] [[3]]

local function exercise(mode)
    local log = {}
    local function acquire(name)
        log[#log + 1] = "open:" .. name
        return setmetatable({ name = name }, {
            __close = function(value)
                log[#log + 1] = "close:" .. value.name
            end,
        })
    end

    if mode == 0 then
        goto first_exit
    end
    do
        local first <close> = acquire("first")
        do
            local inner <close> = acquire("inner")
            log[#log + 1] = "side:" .. first.name .. ":" .. inner.name
            if mode == 1 then
                goto first_exit
            end
            if mode == 2 then
                goto second_exit
            end
            log[#log + 1] = "fallthrough"
        end
        log[#log + 1] = "after-inner"
    end

    ::first_exit::
    log[#log + 1] = "target:first"
    goto sibling
    ::second_exit::
    log[#log + 1] = "target:second"
    ::sibling::
    -- Both exits converge before a fresh sibling scope, which may reuse first's slot.
    do
        local later <close> = acquire("later")
        log[#log + 1] = "body:" .. later.name
    end
    log[#log + 1] = "after-later"
    return table.concat(log, ",")
end

local expected = {
    [0] = "target:first,open:later,body:later,close:later,after-later",
    [1] = "open:first,open:inner,side:first:inner,close:inner,close:first,"
        .. "target:first,open:later,body:later,close:later,after-later",
    [2] = "open:first,open:inner,side:first:inner,close:inner,close:first,"
        .. "target:second,open:later,body:later,close:later,after-later",
    [3] = "open:first,open:inner,side:first:inner,fallthrough,close:inner,after-inner,"
        .. "close:first,target:first,open:later,body:later,close:later,after-later",
}
for mode = 0, 3 do
    local actual = exercise(mode)
    assert(actual == expected[mode], actual)
    print("regress_480_cleanup_ownership", mode, actual)
end
