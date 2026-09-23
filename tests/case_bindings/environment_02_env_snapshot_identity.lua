-- regress_259_env_snapshot_identity#1: 保存的旧 _ENV 不能在重绑定后被误写成当前 global
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=0]]
-- unluac: expect-contains [[_ENV = {]]
-- unluac: expect-contains [[destination = { value = source.value }]] [[@debug=retained]]
local original_env = _ENV
original_env.regress_259_saved_marker = "original"
_ENV = {
    regress_259_saved_marker = "redirected",
    print = original_env.print,
}
original_env.assert(original_env.regress_259_saved_marker == "original")
original_env.assert(regress_259_saved_marker == "redirected")
print("regress_259_env_snapshot_identity#1", original_env.regress_259_saved_marker)
_ENV = original_env
original_env.regress_259_saved_marker = nil

-- 字段 getter 必须先读完旧 upvalue，完整表才能安装到该 cell；只读一次。
local function observe_install()
    local destination = "before"
    local reads = 0
    local function install(source)
        destination = { value = source.value }
    end
    local source = setmetatable({}, {
        __index = function(_, key)
            assert(destination == "before" and key == "value")
            reads = reads + 1
            return "after"
        end,
    })
    install(source)
    assert(destination.value == "after" and reads == 1)
    print("environment-install", destination.value, reads)
end
observe_install()
