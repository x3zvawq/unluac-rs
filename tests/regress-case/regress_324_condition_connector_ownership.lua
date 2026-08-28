local RateUs = {}

RateUs.isAvailable = function()
    if GFunc.isOpenstor() then
    else
        if not GFunc.isOfficialChannel() then
            return false
        end
    end
    return RateUs.status == 1 and 30 <= require("app.main.player").lv()
end

return RateUs
