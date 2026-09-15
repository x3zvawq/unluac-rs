-- 模板键集合与后续字段写入不同；静态化新的稀疏 key 会提前改变 hash/array 扩容。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[table-constructor]] [[5]]
-- TDUP 常量 hash 按稳定键身份展示；后续运行时字段仍保留原写入次序。
-- unluac: expect-contains [[left = true, right = true]] [[@dialect=luajit]]
local function build(a)
    local value = true
    local t = {true, [5] = value}
    t[2] = a
    t[4] = a
    return t
end
local function build_hash(a)
    local value = true
    local t = {true, left = true, right = true, [8] = value}
    t[2] = a
    t[4] = a
    return t
end
local function run(f, a)
    local t = assert(loadstring(string.dump(f)))(a)
    print(#t, t[0], t[1], t[2], t[3], t[4], t[5], t[8], t.left, t.right, t.marker)
end
local function static_hash(a)
    local t = {true, [5] = true, marker = nil}
    t.marker = a
    t[2] = a
    t[4] = a
    return t
end
local function runtime_name(a)
    local key = "marker"
    local t = {true, [key] = true}
    t[2] = a
    t[5] = true
    return t
end
local function zero_slot(a)
    local t = {[0] = true}
    t[2] = a
    t[4] = a
    return t
end
run(build, nil)
run(build, false)
run(build_hash, nil)
run(build_hash, false)
run(static_hash, nil)
run(static_hash, false)
run(runtime_name, nil)
run(runtime_name, false)
run(zero_slot, nil)
run(zero_slot, false)
