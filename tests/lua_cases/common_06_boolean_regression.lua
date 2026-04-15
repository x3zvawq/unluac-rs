-- common_06_boolean_regression#1: 共享主语短路分支
local function test_shared_subjects()
    function f(player)
      local bCanAuto = true
      if bCanAuto then
        local nType = 1
        if nType > 0 then
          local nLandIndex = GetHomelandMgr().IsCommunityMember(player.dwID)
          if nLandIndex and nLandIndex > 0 then
            player.SetTimer(3 * 16, "scripts/Include/repro.lua", nLandIndex, nType)
          end
        end
      end
    end
end

-- common_06_boolean_regression#2: 相邻结果槽内联
local function test_adjacent_sinks()
    function repro(player)
        local active = IsActivityOn(936)
        local picked = active and 1 or 0
        if picked > 0 then
            local land = GetHomelandMgr().IsCommunityMember(player.dwID)
            if land and land > 0 then
                player.SetTimer(48, "scripts/Include/repro.lua", land, picked)
            end
        end
    end
end

-- common_06_boolean_regression#3: 自赋值分支壳
local function test_self_assign()
    local log = {}

    local function mark(tag, value)
        log[#log + 1] = tag
        return value
    end

    local a = "x"

    if mark("m1", mark("m2", 1)) then
        a = a
    else
        a = "z"
    end

    print("common_06_boolean_regression#3", tostring(a), table.concat(log, ","))
end

-- common_06_boolean_regression#4: 含副作用or分支残余
local function test_impure_or()
    local log = {}

    local function mark(tag, value)
        log[#log + 1] = tag
        return value
    end

    local a = "x"
    local d = "y"

    if mark("m2", 1) or d then
        a = a
    else
        a = d
    end

    print("common_06_boolean_regression#4", tostring(a), tostring(d), table.concat(log, ","))
end

-- common_06_boolean_regression#5: 退化guard链
local function test_degenerate_guard()
    -- Exercises `(A or B) and C` patterns where the `and C` guard compiles to a
    -- degenerate TEST block (both CFG edges point to the same successor) because
    -- the if-then body is empty or the guard is the last condition before merge.
    -- The decompiler must fold the degenerate guard back into the short-circuit
    -- condition instead of silently dropping it.

    local a = 1
    local b = true

    -- Case 1: empty body – `and b` produces a degenerate TEST block
    if (a == 1 or a == 2) and b then
    end

    -- Case 2: non-empty body
    if (a == 1 or a == 2) and b then
        print("common_06_boolean_regression#5")
    end

    -- Case 3: longer or-chain with trailing guard
    if (a == 1 or a == 2 or a == 3) and b then
        print("common_06_boolean_regression#5")
    end
end

test_shared_subjects()
test_adjacent_sinks()
test_self_assign()
test_impure_or()
test_degenerate_guard()
