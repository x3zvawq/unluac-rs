local makers = {}

for outer = 1, 4 do
    local base = outer * 2LL

    makers[#makers + 1] = function(limit)
        local value = base
        local step = 0

        ::tick::
        step = step + 1

        if step > limit then
            return tostring(value)
        end

        if (step + outer) % 2 == 0 then
            value = value + step + 1LL
            goto tick
        end

        value = value * 2LL - step
        goto tick
    end
end

local out = {}

for i = 1, #makers do
    out[i] = makers[i](i + 2)
end

print("luajit-closure-label", table.concat(out, ","))
