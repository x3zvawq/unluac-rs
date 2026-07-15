-- regress_183_mixed_irreducible_explicit_close#1: cleanup 出边不能吞掉 island 目标 label
-- unluac: expect-contains [[<close>]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]

return function(a, b, c)
    do
        local guard <close> = closer()
        if a then
            goto left
        end
        goto right

        ::left::
        if b then
            goto done
        end
        goto right

        ::right::
        if c then
            goto done
        end
        goto left
    end

    ::done::
    return 1
end
