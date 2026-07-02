-- unluac: expect-contains [["global"](]]
-- unluac: expect-not-contains [[:global(]]
local log = {}
local object = {
    ["global"] = function(self, value)
        log[#log + 1] = value
    end,
}

object:global("ok")

print("regress_62_keyword_method_name", table.concat(log, ","))
