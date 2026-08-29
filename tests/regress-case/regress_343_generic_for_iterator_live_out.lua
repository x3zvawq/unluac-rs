-- regress_343_generic_for_iterator_live_out: loop 后仍读取的 iterator producer 不能被删除。
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[unresolved]]

local function make_iterator(label)
    local emitted = false
    return function()
        if emitted then
            return nil
        end
        emitted = true
        return label
    end, nil, nil
end

local function run()
    local iterator, state, control = make_iterator("live")
    for _ in iterator, state, control do
    end
    return type(iterator), state == nil, control == nil
end

print("regress_343_generic_for_iterator_live_out", run())
