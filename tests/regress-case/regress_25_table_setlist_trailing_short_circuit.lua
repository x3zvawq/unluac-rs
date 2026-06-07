-- regress_25_table_setlist_trailing_short_circuit#1: SETLIST 尾部多返回里的短路左值 producer 可以折回构造器
-- unluac: expect-contains [[themeLayerTags = { tostring(]]
-- unluac: expect-contains [[background or 0]]
-- unluac: expect-not-contains [[unluac error]]
local function build_tags(loaded)
    local objects = {}
    if not loaded.themeLayertags then
        objects.themeLayerTags = { tostring(loaded.background or 0) }
    else
        objects.themeLayerTags = loaded.themeLayerTags
    end
    return objects.themeLayerTags[1]
end

print("regress_25_table_setlist_trailing_short_circuit#1", build_tags({ background = false }))
