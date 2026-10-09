-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-ast-count [[repeat]] [[0]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]] [[@dialect=lua5.1]]
local function apply(caster, ids)
    for i = 1, #ids do
        local member = Find(ids[i])
        if member then
            if member.id == caster.id then
                member.Add(2)
            else
                local a = member.Has(2, 1)
                local b = caster.Has(2, 1)
                if (b and a) or (not b and not a) then
                    member.Add(1)
                end
            end
        end
    end
end

local events, members, member_value, caster_value
local function record(value) events[#events + 1] = value end
local caster = {
    id = 1,
    Has = function(kind, level)
        assert(kind == 2 and level == 1)
        record("caster")
        return caster_value
    end
}
members = {
    {
        id = 1,
        Add = function(level) record("self" .. level) end,
        Has = function() error("self query") end
    },
    {
        id = 2,
        Add = function(level) record("other" .. level) end,
        Has = function(kind, level)
            assert(kind == 2 and level == 1)
            record("member")
            return member_value
        end
    }
}
function Find(id)
    record("find" .. id)
    return members[id]
end
local function check(a, b, matched)
    events, member_value, caster_value = {}, a, b
    apply(caster, { 3, 1, 2, 2, 1 })
    local other = matched and ",other1" or ""
    local expected = "find3,find1,self2,find2,member,caster" .. other
        .. ",find2,member,caster" .. other .. ",find1,self2"
    assert(table.concat(events, ",") == expected)
    print("loop-arm", tostring(a), tostring(b), matched, expected)
end
check(nil, nil, true)
check(nil, false, true)
check(false, nil, true)
check(false, false, true)
check(true, true, true)
check(0, "", true)
check("", 0, true)
check(nil, true, false)
check(true, nil, false)
check(false, 0, false)
check(0, false, false)
events = {}
apply(caster, {})
assert(#events == 0)
print("empty-loop", #events)
