-- 独立不可规约区域不得让所有 SSA carrier 的空声明累积到函数入口。
-- 33 段足以让旧生成结果超过 Lua 的 200 个活跃 local 上限；原源码只复用少数槽。
local function run(entry, cycle)
    local total = 0
    do local n = 0; if entry then goto second1 end; ::first1:: total = total + 1; ::second1:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first1 end end
    do local n = 0; if entry then goto second2 end; ::first2:: total = total + 1; ::second2:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first2 end end
    do local n = 0; if entry then goto second3 end; ::first3:: total = total + 1; ::second3:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first3 end end
    do local n = 0; if entry then goto second4 end; ::first4:: total = total + 1; ::second4:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first4 end end
    do local n = 0; if entry then goto second5 end; ::first5:: total = total + 1; ::second5:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first5 end end
    do local n = 0; if entry then goto second6 end; ::first6:: total = total + 1; ::second6:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first6 end end
    do local n = 0; if entry then goto second7 end; ::first7:: total = total + 1; ::second7:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first7 end end
    do local n = 0; if entry then goto second8 end; ::first8:: total = total + 1; ::second8:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first8 end end
    do local n = 0; if entry then goto second9 end; ::first9:: total = total + 1; ::second9:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first9 end end
    do local n = 0; if entry then goto second10 end; ::first10:: total = total + 1; ::second10:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first10 end end
    do local n = 0; if entry then goto second11 end; ::first11:: total = total + 1; ::second11:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first11 end end
    do local n = 0; if entry then goto second12 end; ::first12:: total = total + 1; ::second12:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first12 end end
    do local n = 0; if entry then goto second13 end; ::first13:: total = total + 1; ::second13:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first13 end end
    do local n = 0; if entry then goto second14 end; ::first14:: total = total + 1; ::second14:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first14 end end
    do local n = 0; if entry then goto second15 end; ::first15:: total = total + 1; ::second15:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first15 end end
    do local n = 0; if entry then goto second16 end; ::first16:: total = total + 1; ::second16:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first16 end end
    do local n = 0; if entry then goto second17 end; ::first17:: total = total + 1; ::second17:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first17 end end
    do local n = 0; if entry then goto second18 end; ::first18:: total = total + 1; ::second18:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first18 end end
    do local n = 0; if entry then goto second19 end; ::first19:: total = total + 1; ::second19:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first19 end end
    do local n = 0; if entry then goto second20 end; ::first20:: total = total + 1; ::second20:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first20 end end
    do local n = 0; if entry then goto second21 end; ::first21:: total = total + 1; ::second21:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first21 end end
    do local n = 0; if entry then goto second22 end; ::first22:: total = total + 1; ::second22:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first22 end end
    do local n = 0; if entry then goto second23 end; ::first23:: total = total + 1; ::second23:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first23 end end
    do local n = 0; if entry then goto second24 end; ::first24:: total = total + 1; ::second24:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first24 end end
    do local n = 0; if entry then goto second25 end; ::first25:: total = total + 1; ::second25:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first25 end end
    do local n = 0; if entry then goto second26 end; ::first26:: total = total + 1; ::second26:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first26 end end
    do local n = 0; if entry then goto second27 end; ::first27:: total = total + 1; ::second27:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first27 end end
    do local n = 0; if entry then goto second28 end; ::first28:: total = total + 1; ::second28:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first28 end end
    do local n = 0; if entry then goto second29 end; ::first29:: total = total + 1; ::second29:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first29 end end
    do local n = 0; if entry then goto second30 end; ::first30:: total = total + 1; ::second30:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first30 end end
    do local n = 0; if entry then goto second31 end; ::first31:: total = total + 1; ::second31:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first31 end end
    do local n = 0; if entry then goto second32 end; ::first32:: total = total + 1; ::second32:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first32 end end
    do local n = 0; if entry then goto second33 end; ::first33:: total = total + 1; ::second33:: total = total + 10; n = n + 1; if cycle and n < 2 then goto first33 end end
    return total
end
assert(run(true, false) == 330)
assert(run(false, true) == 726)
print("regress_476_irreducible_scope_pressure", run(true, false), run(false, true))
