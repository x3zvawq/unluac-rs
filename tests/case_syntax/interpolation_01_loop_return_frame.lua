-- 循环控制槽退休后，插值仍须在高槽调用 format，再复制到低返回槽。
-- unluac: expect-ast-max [[local-binding]] [[4]] [[@proto=1]] [[@debug=stripped]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]]
local function render(seed, values, observe)
    local acc = seed
    local marks = {}
    for index, value in ipairs(values) do
        acc += value
        marks[index] = tostring(acc)
    end
    return `% \{escaped\} \` \\ \255 seed={observe(seed)} acc={observe(acc)} marks={observe(table.concat(marks, ","))}`
end
local trace = {}
local function observe(value)
    trace[#trace + 1] = tostring(value)
    return value, "extra"
end
assert(render(5, {1, 2}, observe) == "% {escaped} ` \\ \255 seed=5 acc=8 marks=6,8")
assert(render(7, {}, observe) == "% {escaped} ` \\ \255 seed=7 acc=7 marks=")
print(render(7, {3}, observe))
assert(#trace == 9 and table.concat(trace, "|") == "5|8|6,8|7|7||7|10|10")
