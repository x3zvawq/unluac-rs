local function build(seed)
    return {
        branch = {
            [seed] = function(x)
                return seed + x
            end,
        },
        pick = function(self, key)
            return self.branch[key]
        end,
    }
end

local obj = build(4)
local fn = obj:pick(4)

print("table-call", fn(8), obj.branch[4](2))
