-- regress_312_cross_block_direct_snapshot: 跨块 exit copy 必须保留已覆写 carried temp 的快照
-- PUC 的 until false 仍有 LOADBOOL/TEST；LuaJIT 已将它编译为无条件回边。
-- unluac: expect-not-contains [[if false then]] [[@dialect=luajit]]

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
