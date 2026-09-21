-- 结构计数来自最终 AST：字符串里的关键字不算节点，proto 作用域不包含子函数体。
-- unluac: expect-count [[@literal-if-while-function]] [[1]]
-- unluac: expect-instruction-count [[not]] [[0]]
-- unluac: expect-min-count [[assert(]] [[2]]
-- unluac: expect-max-count [[@literal-if-while-function]] [[1]]
-- unluac: expect-contains [[@literal-if-while-function]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[function]] [[1]] [[@proto=0]]
-- unluac: expect-ast-count [[function]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[function]] [[0]] [[@proto=2]]
-- local-binding 包含命名函数、普通声明和 for binding；不把函数参数或子函数成员算入父域。
-- unluac: expect-ast-count [[local-binding]] [[5]] [[@proto=0]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
-- assign 不把声明初始化或字符串里的等号计为赋值。
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=0]] [[@debug=retained]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-function]] [[1]] [[@proto=1]]
-- unluac: expect-ast-max [[while]] [[0]]
-- unluac: expect-ast-min [[call]] [[1]] [[@proto=0]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@debug=stripped]] [[@variant=default]]
-- unluac: expect-ast-count [[close-binding]] [[0]]
-- unluac: expect-ast-count [[global-decl]] [[0]]
-- unluac: expect-ast-count [[named-vararg-function]] [[0]]
-- unluac: expect-ast-count [[table-constructor]] [[4]] [[@proto=0]]
-- unluac: expect-ast-count [[table-list-field]] [[4]]
-- unluac: expect-ast-count [[table-record-field]] [[3]]
-- unluac: expect-ast-count [[table-constructor]] [[0]] [[@proto=1]]
-- unluac: expect-contains [[local function outer()]] [[@debug=retained]]
-- unluac: expect-not-contains [[local function outer()]] [[@debug=ignored]]
-- 含不同级别的闭括号，验证原样匹配而非截断后误吞下一个参数。
-- unluac: expect-count [==[@brackets:]]=]:end]==] [[1]]
local function outer()
    return function() end
end
assert(type(outer()) == "function")
assert(outer()() == nil)
print("readability_assertion_protocol", "@literal-if-while-function")
print("@brackets:]]=]:end")
print("<close> global function(a, ...named) end")
-- 同时覆盖值与 key 中的嵌套构造器；字符串中的伪字段不参与计数。
local rows = { { 1, 2 }, key = { value = 3 }, [{ 4 }] = 5 }
assert(rows[1][2] == 2 and rows.key.value == 3)
local table_keys = 0
for key, value in pairs(rows) do
    if type(key) == "table" then
        assert(key[1] == 4 and value == 5)
        table_keys = table_keys + 1
    end
end
assert(table_keys == 1)
print("{ fake = { 1, 2 }, [3] = 4 }")
