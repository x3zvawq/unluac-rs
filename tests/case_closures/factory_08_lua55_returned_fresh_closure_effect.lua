-- A fresh closure returned by a known factory must retain its projected call effect.

local weak
local rooted_during_condition

local function reset_probe()
    weak = setmetatable({}, { __mode = "v" })
    rooted_during_condition = false
end

local function condition()
    collectgarbage("collect")
    rooted_during_condition = weak[1] ~= nil
    return true
end

local function probe()
    reset_probe()
    global returned_closure_marker = 0
    repeat
        global<const> *
        print("regress445-returned-fresh-closure")
        local item
        local function initialize()
            item = {}
            weak[1] = item
        end
        local function factory()
            return function()
                initialize()
            end
        end
        local holder = factory()
        holder()
        returned_closure_marker = 1
    until condition()
    return rooted_during_condition
end

assert(probe(), "returned fresh closure call lost its captured root effect")
print("regress_445_lua55_returned_fresh_closure_effect", "OK")
