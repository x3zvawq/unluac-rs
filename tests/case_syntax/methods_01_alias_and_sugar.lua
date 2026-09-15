-- regress_322_alias_and_sugar: 字段声明风格与已证明的原调用帧树化。
-- unluac: expect-contains [[return p1_0.first .. " " .. p1_0.last]]
-- unluac: expect-not-contains [[p1_0["]]
-- Method keys only suggest style; parameter identity and lexical scope separately allow self.
-- unluac: expect-contains [[function r2_0:add(p3_1)]]
-- unluac: expect-contains [[function r2_0:value_text()]]
-- unluac: expect-not-contains [[local r0_5 = print]]
-- unluac: expect-contains [[print(r0_4, r0_3:add(2):add(3):value_text())]]

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

assert(rendered == "Ada Lovelace")
print(rendered, counter:add(2):add(3):value_text())
assert(counter.value == 6 and counter:value_text() == "6")
