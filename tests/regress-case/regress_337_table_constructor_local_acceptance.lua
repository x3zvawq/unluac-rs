-- regress_337: fixed call results may be nil, so raw SETLIST must not be split into SETTABLE.

local function run()
    local calls = 0
    local function maybe_nil()
        calls = calls + 1
        return nil
    end

    local values = { "head", (maybe_nil()), "tail" }
    print("regress_337#nil-shape", calls, #values, values[1], values[2], values[3])
end

-- LuaJIT 的模板容量在首次序列化时归一化；两条基线都执行已加载的 chunk，
-- 保留 #table 的真实观察，而不把 source 编译器的内存模板当成字节码运行基线。
if jit then
    run = assert(loadstring(string.dump(run)))
end
run()
