-- regress_259_env_snapshot_identity#1: 保存的旧 _ENV 不能在重绑定后被误写成当前 global
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local original_env = _ENV
original_env.regress_259_saved_marker = "original"
_ENV = {
    regress_259_saved_marker = "redirected",
    print = original_env.print,
}
print("regress_259_env_snapshot_identity#1", original_env.regress_259_saved_marker)
_ENV = original_env
original_env.regress_259_saved_marker = nil
