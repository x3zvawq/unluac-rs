-- regress_312_cross_block_direct_snapshot: 跨块 exit copy 必须保留已覆写 carried temp 的快照
-- unluac: expect-not-contains [[unluac error]]
-- PUC 的 until false 仍有 LOADBOOL/TEST；LuaJIT 已将它编译为无条件回边。
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[break]] [[2]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[break]] [[2]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[break]] [[2]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[break]] [[2]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[break]] [[2]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-not-contains [[if false then]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=1]] [[@dialect=luajit]]

local function snapshot_across_empty_pad(stop, touch)
    local carried = 1
    local count = 0
    local result
    repeat
        if stop then
            break
        end
        result = carried
        carried = carried + 1
        count = count + 1
        if count >= 1 then
            if touch then
                touch = false
            end
            break
        end
    until false
    return result
end

assert(snapshot_across_empty_pad(true, false) == nil)
assert(snapshot_across_empty_pad(false, true) == 1)
assert(snapshot_across_empty_pad(false, false) == 1)
print("regress_312_cross_block_direct_snapshot", "OK")
