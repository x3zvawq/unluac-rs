local ffi = require("ffi")

ffi.cdef([[
typedef struct {
    int value;
} counter_t;
]])

local counter_t = ffi.metatype("counter_t", {
    __index = {
        bump = function(self, delta)
            self.value = self.value + delta
            return self.value
        end,
    },
})

local state = counter_t(3)
local acc = 1LL

for i = 1, 5 do
    acc = acc + state:bump(i)
end

print("luajit-metatype", state.value, tostring(acc))
