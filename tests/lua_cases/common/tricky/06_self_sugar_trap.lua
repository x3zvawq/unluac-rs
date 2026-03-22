local function self_sugar_trap(obj)
    obj:method1():method2(obj.prop)

    local temp = obj.method3
    temp(obj)

    return obj
end

local obj = {
    prop = 7,
}

function obj:method1()
    print("self", "m1", self.prop)
    return self
end

function obj:method2(value)
    print("self", "m2", self.prop, value)
    return self
end

function obj.method3(self)
    print("self", "m3", self.prop)
end

print("self", self_sugar_trap(obj) == obj)
