local obj = {
    base = 1,
}

function obj:push(...)
    local args = { ... }
    self.base = self.base + #args + args[1]
    return self, args[#args]
end

function obj:read(extra)
    return self.base + extra
end

local chain, last = obj:push(3, 4, 5)
print("method-vararg", chain:read(last), last, obj.base)
