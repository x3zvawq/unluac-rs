-- Aligned tables whose fields hold function values always expand one entry
-- per line: function bodies contain hard line breaks, so a packed content
-- line would glue the following fields onto the broken function's lines
-- (e.g. `end, kind = 3` or the nested `end }, [2] = {` shape) and produce
-- over-long, misindented rows.
-- unluac: expect-not-contains [[end },]]
-- unluac: expect-not-contains [[end, kind]]
-- unluac: expect-not-contains [[end, buy]]
-- unluac: expect-contains [[    run  = function()]]
-- unluac: expect-contains [[    kind = 3,]]
-- unluac: expect-contains [[  [2] = {]]
-- unluac: expect-contains [[    call   = function()]]
local cfg = {
    id = 7,
    name = "box",
    run = function()
        return 42
    end,
    kind = 3,
    buy = function()
        return 11
    end,
}
local routes = {
    [1] = {
        weight = 5,
        call = function()
            return 10
        end,
    },
    [2] = {
        weight = 6,
        call = function()
            return 20
        end,
    },
}
print(cfg.id, cfg.run(), routes[1].weight, routes[2].call())
