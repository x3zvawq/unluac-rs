-- regress_08_global_table_install_readability#1: inline recovered aliases in table field installs
-- unluac: expect-contains [[return { objectName = p1_0, eggName = p1_1, hidden = p1_2 == true }]]
-- unluac: expect-not-contains [[r1_0.objectName]]
-- unluac: expect-ast-count [[table-constructor]] [[3]]
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-count [[local-binding]] [[0]]
g_level_scripts = {}

function make_level(object_name, egg_name, hidden)
    print("regress_08_global_table_install_readability#1", object_name, egg_name, hidden == true)
    return {
        objectName = object_name,
        eggName = egg_name,
        hidden = hidden == true,
    }
end

g_level_scripts.LevelP4_440 = make_level("ExtraGoldenEgg_1", "LevelGE_9")
g_level_scripts.LevelP4_444 = make_level("ExtraRubberDuck_1", "LevelGE_10", true)

g_level_scripts.LevelP4_426 = {
    onLoadLevel = function()
        print("regress_08_global_table_install_readability#1", "load")
    end,
    onBeforeLevelEnding = function()
        print("regress_08_global_table_install_readability#1", "end")
    end,
}

g_level_scripts.LevelP4_426.onLoadLevel()
g_level_scripts.LevelP4_426.onBeforeLevelEnding()
print("regress_08_global_table_install_readability#1", g_level_scripts.LevelP4_440.objectName)
assert(g_level_scripts.LevelP4_440.objectName == "ExtraGoldenEgg_1")
assert(g_level_scripts.LevelP4_444.hidden == true)

assert(g_level_scripts.LevelP4_440.eggName == "LevelGE_9" and g_level_scripts.LevelP4_440.hidden == false)
assert(g_level_scripts.LevelP4_444.objectName == "ExtraRubberDuck_1" and g_level_scripts.LevelP4_444.eggName == "LevelGE_10")
