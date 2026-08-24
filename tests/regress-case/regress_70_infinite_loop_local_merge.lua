-- unluac: expect-contains [[while true do]]
-- unluac: expect-contains [[show_overlay()]]
-- unluac: expect-contains [[hide_overlay()]]
-- unluac: expect-contains [[r0_0 = screen_pressed()]]
-- unluac: expect-not-contains [[goto]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[repeat]]
-- unluac: expect-not-contains [[unluac error]]

local last_pressed = false
local pressed_edge = false

local function run()
    while true do
        if overlay_enabled() then
            if overlay_hidden() then
                hide_overlay()
            else
                show_overlay()
            end
        else
            hide_overlay()
        end

        if screen_pressed() and not last_pressed then
            pressed_edge = true
        else
            pressed_edge = false
        end
        last_pressed = screen_pressed()
    end
end
