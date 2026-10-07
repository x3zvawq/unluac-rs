-- unluac: expect-contains [[中文]]
-- unluac: expect-not-contains [[\214\208]]
local function render(value)
    return `\214\208\206\196{value}%\{\}`
end
assert(render(17) == "\214\208\206\19617%{}")
print("readable-interpolation-ok")
