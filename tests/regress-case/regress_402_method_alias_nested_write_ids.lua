-- regress_402_method_alias_nested_write_ids: child direct writes do not target an outer same-numbered alias
-- unluac: expect-contains [[:m()]]

local function run(obj)
    local receiver = obj
    receiver.m(receiver)

    local function later(flag, side, other, use)
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

local calls = 0
local receiver = {
    m = function(self)
        calls = calls + 1
        assert(self.tag == "receiver")
    end,
    tag = "receiver",
}
local later = run(receiver)
local left, right = {}, {}
local seen = {}
local function record(value)
    seen[#seen + 1] = value
end
assert(later(true, function() return left end, function() return right end, record) == left)
assert(later(false, function() return left end, function() return right end, record) == right)
assert(calls == 1 and seen[1] == left and seen[2] == right)
