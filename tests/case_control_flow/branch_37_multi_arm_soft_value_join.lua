-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-ast-count [[repeat]] [[0]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[call]] [[5]] [[@proto=1]] [[@dialect=lua5.1]]
local function relocate(id, cause, line)
    local position = {}
    if id == 1 then
        position = One()
    elseif id == 2 or id == 3 then
        position = Two()
    elseif id == 4 then
        position = Three()
    elseif id == 5 then
        position = Four()
    else
        return
    end
    if position and cause == 0 then
        Move(position[line][1], position[line][2], position[line][3])
    end
end

local events, selected, expected_line, moves
local function record(value) events[#events + 1] = value end
function One() record("one"); return selected end
function Two() record("two"); return selected end
function Three() record("three"); return selected end
function Four() record("four"); return selected end
function Move(x, y, z)
    record("move")
    moves = moves + 1
    assert(x == expected_line * 10 + 1)
    assert(y == expected_line * 10 + 2)
    assert(z == expected_line * 10 + 3)
end
local rows = { { 11, 12, 13 }, { 21, 22, 23 } }
local position = setmetatable({}, {
    __index = function(_, line)
        record("row" .. line)
        return rows[line]
    end
})
local function check(id, cause, line, value, selector)
    events, selected, expected_line, moves = {}, value, line, 0
    relocate(id, cause, line)
    local expected = selector
    if selector ~= "" and value and cause == 0 then
        expected = expected .. ",row" .. line .. ",row" .. line .. ",row" .. line .. ",move"
        assert(moves == 1)
    else
        assert(moves == 0)
    end
    assert(table.concat(events, ",") == expected)
    print("soft-value-join", tostring(id), cause, line, tostring(value == position), moves, expected)
end
check(1, 0, 1, position, "one")
check(2, 0, 2, position, "two")
check(3, 0, 1, position, "two")
check(4, 0, 2, position, "three")
check(5, 0, 1, position, "four")
check(0, 0, 1, position, "")
check(nil, 0, 1, position, "")
check("2", 0, 1, position, "")
check(2, 1, 1, position, "two")
check(1, 0, 1, nil, "one")
check(3, 0, 1, false, "two")
check(4, 0, 1, nil, "three")
check(5, 0, 1, false, "four")
