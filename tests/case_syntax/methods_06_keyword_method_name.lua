-- unluac: expect-contains [[:global(]]
local log = {}
local object = {
    ["global"] = function(self, value)
        log[#log + 1] = value
    end,
}

object:global("ok")

assert(#log == 1 and log[1] == "ok")
print("regress_62_keyword_method_name", table.concat(log, ","))
