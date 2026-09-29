-- 回边重入函数首块时，该块的首次初始化不是后方 producer 支配的覆盖端点。
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
-- reset、copy 与一个跨轮 holder；源码作用域交接不能逐轮增加匿名副本。
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@debug=retained]] [[@proto=1]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[unresolved]]
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

-- 两种假值各写一次；0 和空字符串都是真值，不能误入 producer。
local writes = 0
local watched = setmetatable({}, {
    __newindex = function(_, key, value)
        -- 回调发生在 copy 的源码作用域之外，再编译后也不能把该声明延长到这里。
        for index = 1, 20 do
            local name = debug.getlocal(2, index)
            if not name then break end
            assert(name ~= "copy", "copy visible after source scope")
        end
        assert(key == "x")
        assert(value == false or value == nil)
        writes = writes + 1
    end,
})
run(watched, false)
assert(writes == 1)
run(watched, nil)
assert(writes == 2)
run(watched, 0)
run(watched, "")
assert(writes == 2)
