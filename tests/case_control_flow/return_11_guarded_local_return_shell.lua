-- regress_384_guarded_local_return_shell: 结构化 return 壳仍可终结 guarded local 的 false path
-- 第二次 next 检查及其未选 arm 仍属于原字节码，不能为合并赋值而删除。
-- unluac: expect-contains [[local r3_0 = r0_0.decrypt(p3_0)]]
-- unluac: expect-contains [[if not r3_0 then]]
-- unluac: expect-contains [[print("dead")]]
-- unluac: expect-contains [[p4_0 = r0_0.decrypt(p4_0)]]
-- unluac: expect-contains [[return r0_0.consume(p4_0)]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=4]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=3]]
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=3]]
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=4]]

local codec = {}

function codec.decrypt(value)
    return value
end

function codec.consume(value)
    return value
end

local function run_block(value, enabled)
    if enabled then
        local next = codec.decrypt(value)
        if next then
            value = next
        else
            if next then
                print("dead")
            else
                return nil
            end
        end
    end
    return codec.consume(value)
end

local function run_if(value, enabled, kind)
    if enabled then
        local next = codec.decrypt(value)
        if next then
            value = next
        else
            if kind then
                return nil
            else
                return false
            end
        end
    end
    return codec.consume(value)
end

assert(run_block("block", true) == "block")
assert(run_block(false, true) == nil)
assert(run_block("disabled", false) == "disabled")
assert(run_if("if", true, false) == "if")
assert(run_if(false, true, true) == nil)
assert(run_if(false, true, false) == false)

local events = ""
codec.decrypt = function(value)
    events = events .. "decrypt;"
    return value, "ignored"
end
codec.consume = function(value)
    events = events .. "consume;"
    return value, nil, "tail"
end
local value, hole, tail = run_block(0, "")
assert(value == 0 and hole == nil and tail == "tail" and events == "decrypt;consume;")
events = ""
value, hole, tail = run_if("", 0, nil)
assert(value == "" and hole == nil and tail == "tail" and events == "decrypt;consume;")
events = ""
assert(select("#", run_block(nil, true)) == 1 and events == "decrypt;")
events = ""
assert(run_if(nil, true, 0) == nil and events == "decrypt;")
events = ""
assert(run_if(nil, true, nil) == false and events == "decrypt;")
events = ""
value, hole, tail = run_if(false, nil, true)
assert(value == false and hole == nil and tail == "tail" and events == "consume;")

-- 更新参数后再尾调用，必须读取 decrypt 的新值；恒等 decrypt 无法暴露误读入口值。
codec.decrypt = function(input)
    assert(input == "encoded")
    events = events .. "decrypt;"
    return "decoded", "ignored"
end
events = ""
value, hole, tail = run_if("encoded", true, false)
assert(value == "decoded" and hole == nil and tail == "tail" and events == "decrypt;consume;")
