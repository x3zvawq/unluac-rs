-- regress_51_method_hint_short_circuit_arg#1: SELF 后夹着短路参数分支时不能丢 method hint
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[:setVisible(]]
-- unluac: expect-not-contains [[r0_0(r0_1,]]

local widget = {
    visible = false,
    setVisible = function(self, visible)
        self.visible = visible
    end,
}

local enabled = true
local hidden = false
widget:setVisible(enabled and not hidden)
print("regress_51_method_hint_short_circuit_arg#1", widget.visible)
