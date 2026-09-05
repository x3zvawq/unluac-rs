-- regress_489_phi_incoming_edge_identity: entry input and parallel physical edges retain distinct phi slots
local function entry(flag)
    while flag do
        flag = false
    end
    return flag
end
local function parallel(flag, value)
    if flag then end
    while value do
        value = false
    end
    return value
end
assert(entry(true) == false)
assert(entry(false) == false)
assert(parallel(true, true) == false)
assert(parallel(false, true) == false)
print("regress_489_phi_incoming_edge_identity", "closed")
