-- unluac: expect-ast-count [[numeric-for]] [[2]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[4]]
-- unluac: expect-ast-count [[error]] [[0]]
-- regress_193_luau_unreachable_numeric_for_control#1: 无限循环会让内层 FORNLOOP 控制块不可达
-- unluac: expect-contains [[ = 771751936, _ do]]
-- unluac: expect-contains [[ = 771751936, 0 do]]
-- unluac: expect-contains [[while true do]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local function run()
    for outer = 771751936, _ do
        for inner = 771751936, 0 do
            while true do
            end
        end
    end
    return "done"
end

_ = 0
local result = run()
assert(result == "done")
_ = 771751936
assert(run() == "done")
print("regress_193_luau_unreachable_numeric_for_control#1", result)
