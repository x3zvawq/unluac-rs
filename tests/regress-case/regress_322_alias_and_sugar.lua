-- regress_322_alias_and_sugar: stripped alias/field sugar 与 call-result PhysicalRoot 边界
-- unluac: expect-contains [[return p1_0.first .. " " .. p1_0.last]]
-- unluac: expect-not-contains [[p1_0["]]
-- unluac: expect-order [[local r0_5 = print]] [[r0_6 = r0_7.value_text]]
-- unluac: expect-contains [[r0_5(r0_4, r0_6(r0_7))]]

local function display_name(user)
    local first = user["first"]
    local last = user["last"]
    local full = first .. " " .. last

    return full
end

local function make_counter(start)
    local box = { value = start }

    function box:add(delta)
        self.value = self.value + delta
        return self
    end

    function box:value_text()
        return tostring(self["value"])
    end

    return box
end

local user = {
    ["first"] = "Ada",
    ["last"] = "Lovelace",
}

local counter = make_counter(1)
local rendered = display_name(user)

print(rendered, counter:add(2):add(3):value_text())
