-- Original regression by ItsLucas <itslucas@itslucas.me>, PR #35.
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]
-- Nested forward exits must preserve the short-circuit condition and both continuations.
local function f(a,b,c)
local x=0
if a and (b or c) then
if not b then return x end
if (a and b) or c then
x=x+7
else
x=x+4
end
else
if b then
if a then
x=x+7
else
x=x+3
end
else
if not b then
x=x+6
else
x=x+5
end
end
end
return x
end
for i=0,7 do print(f(i%2==1,math.floor(i/2)%2==1,i>=4)) end

-- 折叠前导退出时，条件的短路求值次数与顺序也须保留。
local function observed(a, b, c)
    local trace = ""
    local function mark(name, value)
        trace = trace .. name
        return value
    end
    local result = 0
    if mark("a", a) and (mark("b", b) or mark("c", c)) then
        if not mark("d", b) then return result, trace end
        result = 7
    else
        result = 3
    end
    return result, trace
end
for i = 0, 7 do
    local a, b, c = i % 2 == 1, math.floor(i / 2) % 2 == 1, i >= 4
    local result, trace = observed(a, b, c)
    local expected_result, expected_trace
    if not a then
        expected_result, expected_trace = 3, "a"
    elseif b then
        expected_result, expected_trace = 7, "abd"
    elseif c then
        expected_result, expected_trace = 0, "abcd"
    else
        expected_result, expected_trace = 3, "abc"
    end
    assert(result == expected_result and trace == expected_trace)
    print("nested-escape-order", i, result, trace)
end
