local frame = {}

function guarded_return_chain(kind, key)
    local handled, value, extra = frame.onKeyEvent()
    if not handled and kind == "PRESS" then
        if key == "ESCAPE" or key == "KEY_BACK" then
            record("cancel")
        elseif key == "RETURN" then
            record("return")
        end
    elseif handled then
        return handled, value, extra
    end
    return "BLOCK", nil, kind
end
