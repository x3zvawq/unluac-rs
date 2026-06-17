-- regress_33_table_setlist_binary_producer#1: SETLIST 尾部多返回中的嵌套表字段可消费二元表达式 producer
-- unluac: expect-contains [[x = p5_0.w * 1.5]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[table-set-list]]
local tweens = {}

function tweens.queue(value)
    return value
end

function tweens.callback(value)
    return value
end

function tweens.ease(value)
    return value
end

function tweens.move(value)
    return value
end

local function build_sequence(target)
    local first = tweens.callback({
        callback = function()
            return target.w
        end,
    })
    return tweens.queue({
        first,
        tweens.ease({
            rate = 1,
            interval = tweens.move({
                target = target,
                duration = 300,
                x = target.w * 1.5,
            }),
        }),
    })
end

local result = build_sequence({ w = 2 })
print("regress_33_table_setlist_binary_producer#1", #result, result[2].interval.x)
