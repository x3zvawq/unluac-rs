-- regress_17_generic_for_break_pad#1: generic-for break pad should not be mistaken for terminal exit
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[(function()]]
local show_editor = false

local block_table = {
    themes = {
        classic = true,
        spooky = true,
    },
}

local settings_wrapper = {}
local selected_theme, theme_reads, events = "spooky", 0, {}

function settings_wrapper:getCurrentTheme()
    assert(self == settings_wrapper)
    theme_reads = theme_reads + 1
    return selected_theme
end

local loaded_theme = nil
local particles_loaded = false

local function load_theme_graphics(theme)
    events[#events + 1] = "theme:" .. theme
    loaded_theme = theme
end

local function load_all_theme_graphics()
    events[#events + 1] = "all"
    loaded_theme = "all"
end

local function load_particles(enabled)
    assert(enabled == false)
    events[#events + 1] = "particles"
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
assert(loaded_theme == "spooky" and particles_loaded == false)
assert(theme_reads >= 1 and theme_reads <= 2)
assert(table.concat(events, ",") == "theme:spooky,particles")
print("regress_17_generic_for_break_pad#1", loaded_theme, particles_loaded)

local function check(mode, themes, selected, expected, reads, order)
    show_editor, block_table.themes, selected_theme = mode, themes, selected
    loaded_theme, particles_loaded, theme_reads, events = "unchanged", true, 0, {}
    load_graphics()
    assert(loaded_theme == expected and particles_loaded == false)
    assert(theme_reads == reads and table.concat(events, ",") == order)
end
check(false, {classic = true}, "classic", "classic", 1, "theme:classic,particles")
check(false, {classic = true}, "missing", "unchanged", 1, "particles")
check(false, {}, "spooky", "unchanged", 0, "particles")
check(true, {spooky = true}, "spooky", "all", 0, "all,particles")
check(nil, {spooky = true}, "spooky", "all", 0, "all,particles")
check(0, {spooky = true}, "spooky", "all", 0, "all,particles")
-- 方法查询会改写被捕获的 wrapper；冒号调用仍须向旧 receiver 传递 self。
local saved_wrapper, lookups = settings_wrapper, 0
settings_wrapper = setmetatable({}, {__index = function(receiver, key)
    assert(key == "getCurrentTheme")
    lookups = lookups + 1
    settings_wrapper = {}
    return function(self)
        assert(self == receiver)
        theme_reads = theme_reads + 1
        return selected_theme
    end
end})
check(false, {classic = true}, "classic", "classic", 1, "theme:classic,particles")
assert(lookups == 1)
settings_wrapper = saved_wrapper
-- 混合并行赋值按原逆序写回：表的元方法看到新 selected 和旧 mode，
-- 并且改写 mode 后仍会被这次赋值的末项提交覆盖。
local saved_block, assignment_target, writes = block_table, {}, 0
block_table = setmetatable(assignment_target, {__newindex = function(target, key, value)
    assert(target == assignment_target and key == "themes")
    assert(show_editor == true and selected_theme == "classic")
    writes = writes + 1
    show_editor = "changed during write"
    block_table = {themes = {}}
    rawset(target, key, value)
end})
show_editor = true
check(false, {classic = true}, "classic", "unchanged", 0, "particles")
assert(writes == 1 and assignment_target.themes.classic == true)
assert(show_editor == false)
block_table = saved_block
-- 循环变量之外不需要为同一次冒号调用另造 receiver local。
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=5]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=5]]
-- unluac: expect-ast-count [[method-call]] [[1]] [[@proto=5]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=5]]
-- 重置函数只写入既有绑定，并行赋值不应产生额外源码声明。
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=6]]
-- unluac: expect-ast-count [[local-binding]] [[18]] [[@proto=0]]
