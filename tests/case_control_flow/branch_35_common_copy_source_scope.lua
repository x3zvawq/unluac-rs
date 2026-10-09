-- Branch-local producers may share a phi identity; their copies must stay in scope.
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=3]] [[@dialect=lua5.1]]
strings = { away = "away", dead = "dead", checked = "checked" }
local outputs = {}
local function show(item, value) print("show", item.name, value) end
local function output(item, value)
    outputs[#outputs + 1] = value
    print("output", item.name, value)
end
local function run(window, data)
    local die = window:Lookup("die")
    local items = window:Lookup("items", "")
    local away = data.away == true
    local dead = data.dead == true
    local active = away or dead
    show(die, active)
    show(items:Lookup("out"), dead and not away)
    if active then
        local text
        if away then
            text = strings.away
            show(items:Lookup("found"), false)
        else
            text = strings.dead
            if data.checked then
                text = text .. strings.checked
            end
            show(items:Lookup("found"), data.role == 3)
        end
        output(items:Lookup("text"), text)
    end
    items:Format()
end
local window = { name = "window" }
function window:Lookup(name) return setmetatable({ name = name }, { __index = self }) end
function window:Format() print("format", self.name) end
run(window, { away = true })
run(window, { dead = true })
run(window, { dead = true, checked = true, role = 3 })
run(window, {})
assert(#outputs == 3)
assert(outputs[1] == "away" and outputs[2] == "dead" and outputs[3] == "deadchecked")
