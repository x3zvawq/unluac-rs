local obj = {
    value = 4,
}

function obj:add(n)
    self.value = self.value + n
    return self
end

function obj:read()
    return self.value
end

print("method", obj:add(3):add(2):read(), obj.read(obj))
