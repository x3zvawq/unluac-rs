-- common_09_method_and_self#1: 方法语法糖(:)
local function test_method_sugar()
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

    print("common_09_method_and_self#1", obj:add(3):add(2):read(), obj.read(obj))
end

-- common_09_method_and_self#2: self参数陷阱
local function test_self_trap()
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
        print("common_09_method_and_self#2", "m1", self.prop)
        return self
    end

    function obj:method2(value)
        print("common_09_method_and_self#2", "m2", self.prop, value)
        return self
    end

    function obj.method3(self)
        print("common_09_method_and_self#2", "m3", self.prop)
    end

    print("common_09_method_and_self#2", self_sugar_trap(obj) == obj)
end

-- common_09_method_and_self#3: 方法链与变参
local function test_chain_vararg()
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
    print("common_09_method_and_self#3", chain:read(last), last, obj.base)
end

test_method_sugar()
test_self_trap()
test_chain_vararg()
