-- regress_384_guarded_local_return_shell: 结构化 return 壳仍可终结 guarded local 的 false path
-- unluac: expect-contains [[p3_0 = r0_0.decrypt(p3_0)]]
-- unluac: expect-contains [[p4_0 = r0_0.decrypt(p4_0)]]

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
