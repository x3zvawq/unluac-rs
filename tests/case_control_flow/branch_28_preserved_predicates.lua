-- 前一条路径事实不能删除原字节码中第二次显式 truthiness 检查。
-- unluac: expect-contains [[if a and a.b then]] [[@debug=retained]] [[@dialect=lua5.1]]
-- unluac: expect-contains [[if r1_0 and r1_0.b then]] [[@debug=stripped]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[if]] [[4]]
function fn(cfg, h, id)
    local a = cfg[id]
    if not (h and a) then
        return
    end
    if a and a.b then
        print("ok")
    end
end
fn({}, true, 1)
fn({false}, true, 1)
fn({{b = true}}, false, 1)
fn({{b = false}}, true, 1)
fn({{b = true}}, true, 1)
fn({{b = 0}}, true, 1)

-- 两条边直接汇合仍保留原 TEST，不能以空 body 为由丢掉检查。
local function empty_test(value)
    if value then end
    return value
end

local function effectful_empty_test(value)
    local reads = 0
    local function read()
        reads = reads + 1
        return value
    end
    if read() then end
    return reads
end

assert(empty_test(false) == false)
assert(empty_test(true) == true)
assert(effectful_empty_test(false) == 1)
assert(effectful_empty_test(true) == 1)
