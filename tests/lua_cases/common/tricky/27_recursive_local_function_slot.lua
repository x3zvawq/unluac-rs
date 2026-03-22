local function build_runner()
    local out = {}
    local key = 1

    local function step(n)
        if n <= 0 then
            return 0
        end

        return step(n - 1) + 1
    end

    out[key] = step
    return out
end

local runner = build_runner()
print("recursive-slot", runner[1](4))
