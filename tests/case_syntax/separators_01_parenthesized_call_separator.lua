-- regress_166_parenthesized_call_separator#1: 换行不能把前一赋值与括号开头的调用粘成同一表达式
-- 同一原槽的 nil 初始化与重赋值共用声明，闭包继续捕获该 cell。
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=0]]
-- unluac: expect-contains [[;]]
-- unluac: expect-contains [[(function()]]
-- unluac: expect-not-contains [[unluac error]]
local sink
sink = print;
(function()
    sink("regress_166_parenthesized_call_separator#1")
end)()
