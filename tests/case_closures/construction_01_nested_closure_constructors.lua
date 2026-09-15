-- 原低槽动态 key 不准备额外副本，闭包与嵌套数组按完整构造帧在原槽创建。
-- unluac: expect-not-contains [[= {}]]
-- unluac: expect-contains [[branch = {]]
-- unluac: expect-contains [[pick = function(]]
-- unluac: expect-contains [[steps = {]]
-- unluac: expect-contains [[call = function(]]

local function build_branch(seed)
    return {
        branch = {
            [seed] = function(delta)
                seed = seed + delta
                return seed
            end,
        },
        pick = function(self, key)
            return self.branch[key]
        end,
    }
end

local function build_steps(seed)
    return {
        seed = seed,
        steps = {
            function(value)
                seed = seed + value
                return seed
            end,
            function(value)
                seed = seed * value
                return seed
            end,
        },
        call = function(self, index, value)
            return self.steps[index](value)
        end,
    }
end

local branch = build_branch(4)
local selected = branch:pick(4)
assert(selected == branch.branch[4])
assert(selected(2) == 6)
assert(branch:pick(4)(3) == 9)
assert(branch.branch[6] == nil and branch.branch[9] == nil)

local steps = build_steps(3)
assert(steps:call(1, 2) == 5)
assert(steps:call(2, 4) == 20)
assert(steps:call(1, 1) == 21)
assert(steps.seed == 3)
assert(steps.steps[1] ~= steps.steps[2])
print("regress_635_nested_closure_constructors", selected(1), steps:call(2, 2), steps.seed)
