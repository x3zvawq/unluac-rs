-- regress_464_lookup_root_overwrite_chain: 复用 owner 的 lookup 必须保留后继释放端点。
-- unluac: expect-not-contains [[unluac error]]
local weak = setmetatable({}, { __mode = "v" })
local storage = {}
local observed = false
local env = setmetatable({}, {
    __index = function(_, name)
        if name == "key" then
            storage.source = nil
        end
        return storage[name]
    end,
    __newindex = function(_, name, value)
        storage[name] = value
        if name == "source" then
            weak[1] = value
        elseif name == "hits" then
            collectgarbage("collect")
            collectgarbage("collect")
            assert(weak[1] == nil, "lookup receiver outlived its physical home")
            observed = true
        end
    end,
})

local function run(_ENV)
    source = { key = 41 }
    key = "key"
    local lookup = source[key]
    lookup_result = 1 + lookup
    hits = 0
end
if setfenv then
    setfenv(run, env)
end
run(env)
assert(observed and storage.lookup_result == 42)
print("regress_464_lookup_root_overwrite_chain", "OK")
