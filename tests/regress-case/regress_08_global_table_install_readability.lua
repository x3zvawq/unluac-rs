-- regress_08_global_table_install_readability#1: inline recovered aliases in table field installs
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

-- unluac: expect-contains [[g_level_scripts.LevelP4_440 = make_level("ExtraGoldenEgg_1", "LevelGE_9")]]
-- unluac: expect-contains [[g_level_scripts.LevelP4_444 = make_level("ExtraRubberDuck_1", "LevelGE_10", true)]]
-- unluac: expect-contains [[g_level_scripts.LevelP4_426 = {]]
-- unluac: expect-not-contains [[local r0_]]
