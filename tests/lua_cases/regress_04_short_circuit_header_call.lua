local function check(closeOnCancelKeyHandler)
    if _G.type(closeOnCancelKeyHandler) == "function" and closeOnCancelKeyHandler() then
        return true
    end

    return false
end

return check
