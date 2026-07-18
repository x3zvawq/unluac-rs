-- regress_271_loop_break_soft_phi: effectful break 不能把本轮 branch-value merge 推到 loop 外
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

local trace = {}

local function mark(tag, value)
    trace[#trace + 1] = tag .. value
    return value
end

local function while_merge(a, b, c, d)
    while a < 3 do
        local x
        if b then
            x = mark("L", a + 10)
        elseif c then
            if d then
                mark("B", a)
                break
            end
            x = mark("R", a + 20)
        else
            mark("O", a)
            break
        end
        mark("S", x)
        a = a + 1
    end
    return a
end

local function repeat_merge(a, b, c)
    repeat
        local x
        if b then
            x = mark("RL", a + 30)
        elseif c then
            x = mark("RR", a + 40)
        else
            mark("RO", a)
            break
        end
        mark("RS", x)
        a = a + 1
    until a >= 3
    return a
end

local function while_elseif_merge(a, b1, b2, b3, b4, b5, b6)
    while a < 3 do
        local x
        if b1 then
            x = mark("E1", a + 50)
        elseif b2 then
            x = mark("E2", a + 60)
        elseif b3 then
            mark("EB3", a)
            break
        elseif b4 then
            x = mark("E4", a + 70)
        elseif b5 then
            mark("EB5", a)
            break
        elseif b6 then
            x = mark("E6", a + 80)
        else
            mark("EE", a)
            break
        end
        mark("ES", x)
        a = a + 1
    end
    return a
end

assert(while_merge(1, true, false, false) == 3)
assert(while_merge(1, false, true, false) == 3)
assert(while_merge(1, false, true, true) == 1)
assert(while_merge(1, false, false, false) == 1)
assert(repeat_merge(1, false, true) == 3)
assert(repeat_merge(1, false, false) == 1)
assert(while_elseif_merge(1, false, false, false, true, false, false) == 3)
assert(while_elseif_merge(1, false, false, true, false, false, false) == 1)
assert(while_elseif_merge(1, false, false, false, false, true, false) == 1)
assert(while_elseif_merge(1, false, false, false, false, false, true) == 3)
assert(table.concat(trace, ",") == "L11,S11,L12,S12,R21,S21,R22,S22,B1,O1,RR41,RS41,RR42,RS42,RO1,E471,ES71,E472,ES72,EB31,EB51,E681,ES81,E682,ES82")
print("regress_271_loop_break_soft_phi")
