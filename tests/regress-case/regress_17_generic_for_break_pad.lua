-- regress_17_generic_for_break_pad#1: generic-for break pad should not be mistaken for terminal exit
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local show_editor = false

local block_table = {
    themes = {
        classic = true,
        spooky = true,
    },
}

local settings_wrapper = {}

function settings_wrapper:getCurrentTheme()
    return "spooky"
end

local loaded_theme = nil
local particles_loaded = false

local function load_theme_graphics(theme)
    loaded_theme = theme
end

local function load_all_theme_graphics()
    loaded_theme = "all"
end

local function load_particles(enabled)
    particles_loaded = enabled
end

local function load_graphics()
    if show_editor == false then
        for theme in pairs(block_table.themes) do
            if theme == settings_wrapper:getCurrentTheme() then
                load_theme_graphics(theme)
                break
            end
        end
    else
        load_all_theme_graphics()
    end
    load_particles(false)
end

load_graphics()
print("regress_17_generic_for_break_pad#1", loaded_theme, particles_loaded)
