-- regress_447_lua55_environment_identity: 环境引用不是待补声明的普通 global
-- unluac: expect-contains [[_ENV["end"] = 7]]
-- unluac: expect-contains [[_ENV._ENV = 9]]
-- unluac: expect-not-contains [[global<const> _ENV]]
-- unluac: expect-not-contains [[global _ENV]]
-- unluac: expect-not-contains [[unluac error]]

local function probe()
    global none, assert, print

    _ENV["end"] = 7
    _ENV["_ENV"] = 9
    assert(_ENV["end"] == 7)
    assert(_ENV["_ENV"] == 9)
    print("regress_447_lua55_environment_identity", "OK")
end

probe()
