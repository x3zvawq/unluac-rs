module("legacy_mod", package.seeall)

function banner(name)
    return "hello:" .. name
end

print("module", banner("lua"), _NAME, type(_M) == "table")
