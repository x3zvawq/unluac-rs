-- regress_30_table_setlist_nested_producer#1: SETLIST 队首 producer 的右侧依赖也要随构造器一起消费
-- unluac: expect-contains [[local r5_2 = {]]
-- unluac: expect-contains [[whilst(function()]]
-- unluac: expect-contains [[block())]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[table-set-list]]
local scheduler = {}

function scheduler.action(callback)
    return callback
end

function scheduler.block()
    return "block"
end

function scheduler.whilst(predicate, body)
    return predicate, body
end

function scheduler.sequence(actions)
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

print("regress_30_table_setlist_nested_producer#1", build_state({ name = "popup", visible = true }))
