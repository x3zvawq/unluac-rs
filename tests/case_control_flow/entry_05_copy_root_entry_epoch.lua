-- 回边重入函数首块时，该块的首次初始化不是后方 producer 支配的覆盖端点。
local function run(owner, done)
    ::again::
    do local reset = 0 end
    if done then return end
    do local copy = owner end
    owner.x = done
    done = true
    goto again
end
local object = {}
run(object, false)
assert(object.x == false, "loop write changed")
object.x = nil
run(object, true)
assert(object.x == nil, "initial entry executed the producer")
print("regress_545_copy_root_entry_epoch", "OK")
