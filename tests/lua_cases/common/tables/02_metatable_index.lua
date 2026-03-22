local t = setmetatable({
    present = "yes",
}, {
    __index = function(_, key)
        return "miss:" .. key
    end,
})

print("meta", t.present, t.absent, t.other)
