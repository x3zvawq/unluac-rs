-- 参数回调替换全局 builtin 后，保存的别名仍调用旧值；固定参数和开放包共用此边界。
-- unluac: expect-not-contains [[ = print]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-contains [[environment.math = {]] [[@debug=retained]]
-- unluac: expect-contains [[local maximum = math.max]] [[@debug=retained]]
-- unluac: expect-contains [[return true, "saved"]]
-- unluac: expect-contains [[check(arguments())]] [[@debug=retained]]
-- unluac: expect-contains [[(3, 7)]]
local check = assert
local original_math = math
local maximum = math.max
local maximum_alias = maximum
local environment = getfenv()
local changed = 0
local function arguments()
    environment.assert = function()
        changed = changed + 1
        return false
    end
    environment.math = {
        max = function()
            changed = changed + 10
            return -1
        end,
    }
    return true, "saved"
end

local ok, message = check(arguments())
local high = maximum_alias(3, 7)
environment.assert = check
environment.math = original_math
assert(ok and message == "saved" and high == 7 and changed == 0)
print("saved builtin aliases", ok, message, high, changed)
