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
