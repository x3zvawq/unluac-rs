-- regress_30_table_setlist_nested_producer#1: SETLIST 队首 producer 的右侧依赖也要随构造器一起消费
-- unluac: expect-contains [[.sequence({]]
-- unluac: expect-contains [[whilst(function()]]
-- unluac: expect-contains [[block())]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[table-set-list]]
-- 嵌套调用保留在同一构造器内，只有显式 first 绑定，三个数组元素不展开成写回。
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=5]]
-- unluac: expect-ast-count [[table-list-field]] [[3]] [[@proto=5]]
local scheduler = {}
local trace = ""

function scheduler.action(callback)
    trace = trace .. "action;"
    return callback
end

function scheduler.block()
    trace = trace .. "block;"
    return "block"
end

function scheduler.whilst(predicate, body)
    assert(body == "block")
    trace = trace .. "whilst;"
    return predicate, body
end

function scheduler.sequence(actions)
    trace = trace .. "sequence;"
    return actions
end

local function build_state(popup)
    local first = scheduler.action(function()
        return popup.name
    end)
    popup.state = scheduler.sequence({
        first,
        scheduler.whilst(function()
            return popup.visible
        end, scheduler.block()),
        scheduler.action(function()
            popup.closed = true
        end),
    })
    return popup.state[1]()
end

local popup = {name = "popup", visible = true}
assert(build_state(popup) == "popup")
assert(trace == "action;block;whilst;action;sequence;")
assert(#popup.state == 3 and popup.state[4] == nil)
assert(popup.state[2]() == true)
popup.visible = false
assert(popup.state[2]() == false)
assert(popup.closed == nil)
popup.state[3]()
assert(popup.closed == true)
print("regress_30_table_setlist_nested_producer#1", popup.name, trace)
