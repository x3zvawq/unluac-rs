-- regress_33_table_setlist_binary_producer#1: SETLIST 尾部多返回中的嵌套表字段可消费二元表达式 producer
-- unluac: expect-contains [[x = p5_0.w * 1.5]]
-- unluac: expect-contains [[.callback or]]
-- unluac: expect-contains [[.move)(4)]]
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
assert(#result == 2 and result[2].interval.x == 3)
print("regress_33_table_setlist_binary_producer#1", #result, result[2].interval.x)

local function build_choice(flag)
    return { (flag and tweens.callback or tweens.move)(4) }
end

local true_choice = build_choice(true)
local false_choice = build_choice(false)
assert(true_choice[1] == 4 and false_choice[1] == 4)
print(
    "regress_33_table_setlist_binary_producer#2",
    true_choice[1],
    false_choice[1]
)
