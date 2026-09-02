-- regress_446_nested_capture_local_namespace: 孙闭包的 LocalId 属于子函数，不能误命中父级同号 local
-- unluac: expect-not-contains [[repeat]]

local function consume(_)
end

local function run(skip)
    repeat
        if skip then
            break
        end

        local outer = 1
        consume(function()
            local child = 2
            return function()
                return child
            end
        end)
        assert(outer == 1)
    until true
end

run(false)
run(true)
print("regress_446_nested_capture_local_namespace", "OK")
