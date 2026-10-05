-- regress_33_table_setlist_binary_producer#1: SETLIST 尾部多返回中的嵌套表字段可消费二元表达式 producer
-- unluac: expect-contains [[x = p5_0.w * 1.5]]
-- unluac: expect-contains [[.callback or]]
-- unluac: expect-contains [[.move)(4)]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[table-set-list]]
-- unluac: expect-ast-count [[local-binding]] [[8]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=5]]
-- unluac: expect-ast-count [[table-constructor]] [[4]] [[@proto=5]]
-- unluac: expect-ast-count [[table-record-field]] [[6]] [[@proto=5]]
-- unluac: expect-ast-count [[table-list-field]] [[2]] [[@proto=5]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=7]]
-- unluac: expect-ast-count [[table-list-field]] [[1]] [[@proto=7]]
local trace = ""
local tweens = {}

function tweens.queue(value)
    trace = trace .. "queue;"
    return value
end

function tweens.callback(value)
    trace = trace .. "callback;"
    return value, "callback-tail"
end

function tweens.ease(value)
    trace = trace .. "ease;"
    return value, "ease-tail"
end

function tweens.move(value)
    trace = trace .. "move;"
    return value, "move-tail"
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

local target = { w = 2 }
local result = build_sequence(target)
assert(#result == 3 and result[2].interval.x == 3)
assert(result[2].rate == 1 and result[2].interval.duration == 300)
assert(result[2].interval.target == target)
assert(result[3] == "ease-tail" and result[4] == nil)
assert(trace == "callback;move;ease;queue;")
assert(result[1].callback() == 2)
target.w = 5
assert(result[1].callback() == 5 and result[2].interval.x == 3)
print("regress_33_table_setlist_binary_producer#1", #result, result[2].interval.x)

local function build_choice(flag)
    return { (flag and tweens.callback or tweens.move)(4) }
end

trace = ""
local true_choice = build_choice(true)
local false_choice = build_choice(false)
assert(true_choice[1] == 4 and false_choice[1] == 4)
assert(true_choice[2] == "callback-tail" and true_choice[3] == nil)
assert(false_choice[2] == "move-tail" and false_choice[3] == nil)
assert(trace == "callback;move;")
print(
    "regress_33_table_setlist_binary_producer#2",
    true_choice[1],
    false_choice[1]
)
