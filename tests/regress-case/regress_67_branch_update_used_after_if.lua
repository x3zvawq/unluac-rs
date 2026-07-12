-- unluac: expect-contains [[p4_0 = r0_0.decrypt(p4_0)]]
-- unluac: expect-contains [[p4_0 = r0_0.inflate(p4_0)]]
-- unluac: expect-contains [[return r0_0.decode(p4_0)]]
-- unluac: expect-not-contains [[decode(r2_0)]]
-- unluac: expect-not-contains [[unluac error]]

local codec = {}

function codec.decrypt(value)
    return "dec:" .. tostring(value)
end

function codec.inflate(value)
    return "inf:" .. tostring(value)
end

function codec.decode(value)
    return "json:" .. tostring(value)
end

local function load_value(value, encrypted, compressed)
    if encrypted then
        value = codec.decrypt(value)
        if not value then
            return nil
        end
    end

    if compressed then
        value = codec.inflate(value)
        if not value then
            return nil
        end
    end

    return codec.decode(value)
end

print("regress_67_branch_update_used_after_if#1", load_value("raw", true, true))
