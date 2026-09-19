-- 前一条路径事实不能删除原字节码中第二次显式 truthiness 检查。
-- unluac: expect-contains [[if a and a.b then]] [[@debug=retained]] [[@dialect=lua5.1]]
-- unluac: expect-contains [[if r1_0 and r1_0.b then]] [[@debug=stripped]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]] [[@dialect=lua5.1]]
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
