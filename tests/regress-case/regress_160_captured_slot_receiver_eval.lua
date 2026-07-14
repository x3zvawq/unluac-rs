-- regress_160_captured_slot_receiver_eval#1: callee 求值副作用后重新读取被捕获槽
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local current
local old = setmetatable({}, {
    __index = function(receiver)
        current = {}
        return function(argument)
            return receiver == argument
        end
    end,
})

current = old
print("regress_160_captured_slot_receiver_eval#1", current.method(current))

-- regress_160_captured_slot_receiver_eval#2: for binding capture 复用已有词法 local
local numeric = {}
for index = 1, 2 do
    numeric[index] = function()
        return index
    end
end

local generic = {}
for _, value in ipairs({ 3, 4 }) do
    generic[#generic + 1] = function()
        return value
    end
end

print(
    "regress_160_captured_slot_receiver_eval#2",
    numeric[1](), numeric[2](), generic[1](), generic[2]()
)
