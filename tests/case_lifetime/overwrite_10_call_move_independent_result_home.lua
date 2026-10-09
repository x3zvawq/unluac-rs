-- A CALL result and its lower MOVE target need independent overwrite owners.
-- unluac: expect-ast-min [[while]] [[1]]
local skip_calls, key_calls, value_calls = 0, 0, 0
local function skip(text, pos)
    skip_calls = skip_calls + 1
    print("skip", pos)
    return pos
end
local function key(text, pos)
    key_calls = key_calls + 1
    print("key", pos)
    return text:sub(pos, pos), pos + 1
end
local function value(text, pos)
    value_calls = value_calls + 1
    print("value", pos)
    return { char = text:sub(pos, pos) }, pos + 1
end
local function run(text)
    local pos = skip(text, 1)
    local result = {}
    local length = #text
    while pos <= length do
        local name, after_key = key(text, pos)
        pos = skip(text, after_key)
        if text:sub(pos, pos) ~= ":" then error("colon") end
        pos = skip(text, pos + 1)
        local item, after_value = value(text, pos)
        result[name] = item
        pos = skip(text, after_value)
        if text:sub(pos, pos) == "}" then return result, pos + 1 end
        if text:sub(pos, pos) ~= "," then error("comma") end
        pos = skip(text, pos + 1)
    end
end
local result, pos = run("a:x,b:y}")
assert(result.a.char == "x" and result.b.char == "y" and pos == 9)
assert(skip_calls == 8 and key_calls == 2 and value_calls == 2)
print("independent-result-home", result.a.char, result.b.char, pos)
