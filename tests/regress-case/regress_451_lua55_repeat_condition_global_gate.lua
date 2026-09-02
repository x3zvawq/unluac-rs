-- A collective gate nested in the repeat body does not cover missing globals in until.
-- unluac: expect-contains [[global<const> type]]
-- unluac: expect-contains [[global<const> *]]
-- unluac: expect-order [[global<const> type]] [[global<const> *]]
-- unluac: expect-order [[global<const> *]] [[print("body")]]

local function run(flag)
    global marker = 0
    global<const> assert
    repeat
        global<const> *
        print("body")
        marker = 1
    until type(flag) == "boolean"
    return marker
end

assert(run(true) == 1)
