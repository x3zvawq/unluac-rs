-- regress_184_mixed_irreducible_generic_close#1: island 不能拖垮外层 generic-for owner
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]

return function(a, b, c, factory)
    for item in factory() do
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
