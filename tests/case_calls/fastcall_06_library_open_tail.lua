-- 保存库表后，FASTCALL fallback 在开放尾参数之后读取其字段；回调替换字段必须可见。
-- unluac: expect-contains [[library.max(2, arguments())]] [[@debug=retained]]
-- unluac: expect-not-contains [[ = print]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=3]]
-- unluac: expect-contains [[return first + second + third]] [[@debug=retained]]
local environment = getfenv()
local original_math = math
local trace = ""
environment.math = {
    max = function()
        trace = trace .. "old"
        return -1
    end,
}
local library = math
local function arguments()
    trace = trace .. "args"
    library.max = function(first, second, third)
        trace = trace .. "new"
        return first + second + third
    end
    return 3, 7
end
local result = library.max(2, arguments())
environment.math = original_math
-- O0 普通 CALL 先读旧字段，O1/O2 FASTCALL 在参数之后读新字段；运行比较分别保留该顺序。
print("library open tail", result, trace)
