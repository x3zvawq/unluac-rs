local function build(seed)
    return {
        seed = seed,
        steps = {
            function(x)
                return seed + x
            end,
            function(x)
                return seed * x
            end,
        },
        call = function(self, index, value)
            return self.steps[index](value)
        end,
    }
end

local obj = build(6)
print("table-fn", obj:call(1, 4), obj:call(2, 3), obj.steps[1](1))
