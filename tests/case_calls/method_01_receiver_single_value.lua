-- regress_07_method_receiver_single_value#1: receiver-only method chain should not treat receiver as final arg
-- unluac: expect-not-contains [[(function()]]
-- unluac: expect-min-count [[:]] [[2]]
-- unluac: expect-ast-min [[method-call]] [[2]] [[@proto=1]]
local function test_method_receiver_chain()
    local child = {
        opened = false,
    }
    local root = {}

    function root:getChild(name)
        print("regress_07_method_receiver_single_value#1", name)
        return child
    end

    function child:open()
        self.opened = true
        print("regress_07_method_receiver_single_value#1", self.opened)
    end

    root:getChild("powerup_button"):open()
    assert(child.opened == true)
    print("regress_07_method_receiver_single_value#1", child.opened)
end

test_method_receiver_chain()
