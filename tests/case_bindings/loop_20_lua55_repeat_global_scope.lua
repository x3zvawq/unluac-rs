-- regress_424_lua55_repeat_global_scope: repeat body declarations remain visible to until while missing globals are restored
-- unluac: expect-not-contains [[global<const> *]]

provider = {}

function provider:make()
    return { finish = function() end }
end

function done(value)
    assert(type(value) == "table")
    return true
end

local function run()
    global marker = 0
    repeat
        global<const> done, provider
        local value = provider:make()
        value:finish()
    until done(value)
    return marker
end

local marker = run()
assert(marker == 0)
print("regress_424_lua55_repeat_global_scope", marker)
