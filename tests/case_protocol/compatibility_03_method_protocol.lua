-- regress_306_luajit_method_protocol: LuaJIT split method setup保留receiver快照与call种类
-- unluac: expect-contains [[:collect(1)]]
-- unluac: expect-not-contains [[:dot_call(]]
-- unluac: expect-ast-count [[function]] [[10]]
-- unluac: expect-ast-max [[do-block]] [[0]]

if arg[1] == "--dump-large-method" then
    local source = {}
    local function add_case(name, call)
        source[#source + 1] = "local function " .. name .. "(obj)"
        for index = 1, 260 do
            source[#source + 1] = "do local value = \"method-key-" .. index .. "\" end"
        end
        source[#source + 1] = "return " .. call .. " end"
    end
    add_case("method", "obj:large_method()")
    add_case("dot", "obj.large_method(obj)")
    source[#source + 1] = "return method, dot"
    local dump = string.dump(assert(loadstring(table.concat(source, "\n"))), true)
    if arg[2] then
        local file = assert(io.open(arg[2], "wb"))
        file:write(dump)
        file:close()
    else
        io.write(dump)
    end
    return
end

if arg[1] == "--dump-bypassed-method" then
    local function bypassed_method(obj, enabled)
        if enabled then
            return 0
        end
        return obj:method_call()
    end
    local bit = require("bit")
    local instruction = assert(require("jit.util").funcbc(bypassed_method, 2))
    local function encode_word(word)
        return string.char(
            bit.band(word, 0xff),
            bit.band(bit.rshift(word, 8), 0xff),
            bit.band(bit.rshift(word, 16), 0xff),
            bit.band(bit.rshift(word, 24), 0xff)
        )
    end
    local dump = string.dump(bypassed_method, true)
    local original = encode_word(instruction)
    local patched = bit.bor(instruction, bit.lshift(1, 16))
    local first, last = assert(dump:find(original, 1, true))
    assert(not dump:find(original, last + 1, true))
    dump = dump:sub(1, first - 1) .. encode_word(patched) .. dump:sub(last + 1)
    if arg[2] then
        local file = assert(io.open(arg[2], "wb"))
        file:write(dump)
        file:close()
    else
        io.write(dump)
    end
    return
end

local object = {}
local collected, pair_calls, lookups = 0, 0, 0

function object:collect(...)
    assert(self == object)
    collected = collected + 1
    return ...
end

local function pair()
    pair_calls = pair_calls + 1
    return 4, 5
end

local function fixed_tail(receiver)
    return receiver:collect(1)
end

local function short_tail(receiver, enabled)
    return receiver:collect(enabled and 2 or 3)
end

local function open_tail(receiver)
    return receiver:collect(pair())
end

local current
local old = setmetatable({ tag = "old" }, {
    __index = function(_, key)
        lookups = lookups + 1
        if key == "dot_call" or key == "method_call" then
            current = { tag = "new" }
            return function(self)
                return self.tag
            end
        end
    end,
})
current = old
local dot_result = current.dot_call(current)
current = old
local method_result = current:method_call()
current = old
local open_method_result = current:method_call(pair())

assert(dot_result == "new", dot_result)
assert(method_result == "old", method_result)
assert(open_method_result == "old", open_method_result)
assert(lookups == 3 and pair_calls == 1)
assert(fixed_tail(object) == 1)
assert(short_tail(object, true) == 2)
assert(short_tail(object, false) == 3)
local first, second, extra = open_tail(object)
assert(first == 4 and second == 5 and extra == nil)
assert(collected == 4 and pair_calls == 2)
print(
    "regress_306_luajit_method_protocol",
    fixed_tail(object),
    short_tail(object, true),
    short_tail(object, false),
    open_tail(object)
)
assert(collected == 8 and pair_calls == 3 and lookups == 3)
