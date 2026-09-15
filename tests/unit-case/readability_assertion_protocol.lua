-- 结构计数来自最终 AST：字符串里的关键字不算节点，proto 作用域不包含子函数体。
-- unluac: expect-count [[@literal-if-while-function]] [[1]]
-- unluac: expect-min-count [[assert(]] [[2]]
-- unluac: expect-max-count [[@literal-if-while-function]] [[1]]
-- unluac: expect-contains [[@literal-if-while-function]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[function]] [[1]] [[@proto=0]]
-- unluac: expect-ast-count [[function]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[function]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[empty-function]] [[1]] [[@proto=1]]
-- unluac: expect-ast-max [[while]] [[0]]
-- unluac: expect-ast-min [[call]] [[1]] [[@proto=0]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@debug=stripped]] [[@variant=default]]
-- unluac: expect-ast-count [[close-binding]] [[0]]
-- unluac: expect-ast-count [[global-decl]] [[0]]
-- unluac: expect-ast-count [[named-vararg-function]] [[0]]
-- unluac: expect-contains [[local outer =]] [[@debug=retained]]
-- unluac: expect-not-contains [[local outer =]] [[@debug=ignored]]
local function outer()
    return function() end
end
assert(type(outer()) == "function")
assert(outer()() == nil)
print("readability_assertion_protocol", "@literal-if-while-function")
print("<close> global function(a, ...named) end")
