-- regress_406_method_alias_generic_for: a first iterator may atomically consume its receiver alias
-- unluac: expect-contains [[:each() do]]
-- unluac: expect-contains [[:iterator(),]]

local owner = { values = { 10, 20 } }

function owner:each()
    return ipairs(self.values)
end

local observed = {}

local function collect_values(source)
    local receiver = source
    for _, value in receiver.each(receiver) do
        observed[#observed + 1] = value
    end
end

collect_values(owner)
local result = table.concat(observed, ",")
assert(result == "10,20", result)

local function next_value(values, index)
    index = index + 1
    if values[index] == nil then
        return nil
    end
    return index, values[index]
end

function owner:iterator()
    return next_value
end

local explicit = {}
local function collect_explicit_state(source, values)
    local receiver = source
    for _, value in receiver.iterator(receiver), values, 0 do
        explicit[#explicit + 1] = value
    end
end

collect_explicit_state(owner, owner.values)
local explicit_result = table.concat(explicit, ",")
assert(explicit_result == "10,20", explicit_result)

local function make_ephemeral_owner(state)
    local ephemeral = setmetatable({}, {
        __gc = function()
            state.collected = true
        end,
    })
    ephemeral.touch = function()
        return true
    end
    ephemeral.each = function()
        local emitted = false
        return function()
            if emitted then
                return
            end
            emitted = true
            return true
        end
    end
    return ephemeral
end

local function preserve_call_receiver(source, state)
    local receiver = source
    receiver.touch(receiver)
    source = nil
    collectgarbage("collect")
    assert(not state.collected, "call receiver collected before alias scope ended")
end

local call_state = { collected = false }
preserve_call_receiver(make_ephemeral_owner(call_state), call_state)

local function preserve_loop_receiver(source, state)
    local receiver = source
    for _ in receiver.each(receiver) do
        source = nil
        collectgarbage("collect")
        assert(not state.collected, "loop receiver collected before alias scope ended")
    end
end

local loop_state = { collected = false }
preserve_loop_receiver(make_ephemeral_owner(loop_state), loop_state)

print(
    "regress_406_method_alias_generic_for",
    result,
    explicit_result,
    call_state.collected,
    loop_state.collected
)
