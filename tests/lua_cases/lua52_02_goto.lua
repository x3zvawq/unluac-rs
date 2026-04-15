-- lua52_02_goto#1: goto基础与标签
local function test_goto_label()
    local i = 0

    ::again::
    i = i + 1

    if i < 3 then
        goto again
    end

    print("lua52_02_goto#1", i)
end

-- lua52_02_goto#2: goto模拟break
local function test_goto_break()
    local outer = 0
    local inner = 0
    local total = 0

    while outer < 4 do
        outer = outer + 1
        local j = 0

        while j < 5 do
            j = j + 1
            inner = inner + 1
            total = total + outer + j

            if total > 18 and j > 2 then
                goto done
            end
        end
    end

    ::done::
    print("lua52_02_goto#2", outer, inner, total)
end

-- lua52_02_goto#3: goto模拟continue
local function test_goto_continue()
    local i = 0
    local kept = 0
    local skipped = 0

    while i < 7 do
        i = i + 1

        if i % 2 == 0 then
            skipped = skipped + i
            goto continue
        end

        kept = kept + i
        if kept > 6 then
            skipped = skipped + 100
        end

        ::continue::
    end

    print("lua52_02_goto#3", i, kept, skipped)
end

-- lua52_02_goto#4: 不可规约goto网格
local function test_goto_irreducible()
    local x = 0
    local y = 0

    if x == 0 then
        goto left
    end
    goto right

    ::left::
    x = x + 1
    y = y + 10
    if x < 3 then
        goto right
    end
    goto done

    ::right::
    x = x + 2
    y = y + 1
    if y < 13 then
        goto left
    end

    ::done::
    print("lua52_02_goto#4", x, y)
end

test_goto_label()
test_goto_break()
test_goto_continue()
test_goto_irreducible()
