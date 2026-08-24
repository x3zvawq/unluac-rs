-- regress_166_parenthesized_call_separator#1: 换行不能把前一赋值与括号开头的调用粘成同一表达式
-- unluac: expect-contains [[;]]
-- unluac: expect-contains [[(function()]]
-- unluac: expect-not-contains [[unluac error]]
local sink
sink = print;
(function()
    sink("regress_166_parenthesized_call_separator#1")
end)()
