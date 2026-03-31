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
