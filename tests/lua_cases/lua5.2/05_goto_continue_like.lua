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

print("goto-continue-like", i, kept, skipped)
