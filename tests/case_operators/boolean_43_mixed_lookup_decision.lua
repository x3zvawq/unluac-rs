-- 混合查表、反向谓词和比较在原结果槽形成短路值；返回和调用参数共用证明。
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
local function choose(pair, store, point)
    return pair[1].disposed and not pair[2].disposed and store[point] == pair
end
local function require_pair(pair, store, point)
    assert(pair[1].disposed and not pair[2].disposed and store[point] == pair)
end
local trace, first_value, second_value, matches = '', nil, nil, true
local first = setmetatable({}, {__index = function(_, key)
    assert(key == 'disposed'); trace = trace .. 'a'; return first_value
end})
local second = setmetatable({}, {__index = function(_, key)
    assert(key == 'disposed'); trace = trace .. 'b'; return second_value
end})
local pair = setmetatable({}, {__index = function(_, key)
    trace = trace .. key
    if key == 1 then return first end
    assert(key == 2); return second
end})
local point = {}
local store = setmetatable({}, {__index = function(_, key)
    assert(key == point); trace = trace .. 's'
    if matches then return pair end
end})
for scenario = 1, 7 do
    first_value, second_value, matches = true, false, true
    if scenario == 1 then first_value = nil end
    if scenario == 2 then first_value = false end
    if scenario == 3 then second_value = true end
    if scenario == 4 then first_value = {}; second_value = nil end
    if scenario == 5 then matches = false end
    if scenario == 6 then first_value = 0 end
    if scenario == 7 then first_value = '' end
    trace = ''
    local actual = choose(pair, store, point)
    local expected = true
    if scenario == 1 then expected = nil end
    if scenario == 2 or scenario == 3 or scenario == 5 then expected = false end
    assert(actual == expected)
    local expected_trace = '1a2bs'
    if scenario <= 2 then expected_trace = '1a' end
    if scenario == 3 then expected_trace = '1a2b' end
    assert(trace == expected_trace)
    print('lookup decision', scenario, actual, trace)
    if expected then
        trace = ''
        require_pair(pair, store, point)
        assert(trace == expected_trace)
    end
end

-- Each lookup replaces the same scratch slot; observe roots inside the next lookup.
do
    local weak = setmetatable({}, {__mode = "v"})
    local roots = ""
    local first = setmetatable({}, {__index = function(_, key)
        assert(key == "disposed")
        local value = {}
        weak[1] = value
        return value
    end})
    local second = setmetatable({}, {__index = function(_, key)
        assert(key == "disposed")
        collectgarbage("collect")
        roots = roots .. (weak[1] == nil and "b" or "B")
        return false
    end})
    local pair = setmetatable({}, {__index = function(_, key)
        if key == 1 then return first end
        assert(key == 2)
        collectgarbage("collect")
        roots = roots .. (weak[1] == nil and "p" or "P")
        return second
    end})
    local point = {}
    local store = setmetatable({}, {__index = function(_, key)
        assert(key == point)
        collectgarbage("collect")
        roots = roots .. (weak[1] == nil and "s" or "S")
        return pair
    end})
    assert(choose(pair, store, point))
    assert(roots == "Pbs")
    print("lookup result roots", roots)
    roots = ""
    require_pair(pair, store, point)
    assert(roots == "Pbs")
    print("lookup argument roots", roots)
end
