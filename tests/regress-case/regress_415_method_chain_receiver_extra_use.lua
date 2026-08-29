-- regress_415_method_chain_receiver_extra_use: receiver reused as an argument must retain its binding
-- unluac: expect-not-contains [[:first():finish(]]
-- unluac: expect-contains [[<close>]]

local owner = {}

function owner:first()
    return {
        finish = function(self, same)
            assert(self == same, "method-chain removed the extra receiver use")
        end,
    }
end

local function run()
    local value = owner:first()
    value:finish(value)
end

run()

local close_count = 0
local close_owner = {}

function close_owner:first()
    return setmetatable({
        finish = function() end,
    }, {
        __close = function()
            close_count = close_count + 1
        end,
    })
end

local function close_run()
    local value <close> = close_owner:first()
    value:finish()
    assert(close_count == 0, "method-chain closed the receiver before scope exit")
end

close_run()
assert(close_count == 1, "method-chain deleted the receiver close action")
print("regress_415_method_chain_receiver_extra_use", "OK")
