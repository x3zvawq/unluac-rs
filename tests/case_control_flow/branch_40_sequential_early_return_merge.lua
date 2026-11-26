-- 连续早退分支经 exit-pruned 单臂合流保持线性展开（杜绝 O(2^N) 续段复制），
-- 且块尾 `if ... then <return> else <多句> end` 拍平不产生深层右倾阶梯。
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-max [[if]] [[30]]

local function dispatch_stages(tag, flag, extra, items)
    if tag == "a" and flag then
        if extra == 1 then
            if flag then
                return "a1"
            end
        else
            if extra == 2 then
                return "a2"
            end
        end
    end
    if tag == "b" and flag then
        if extra == 1 then
            if flag then
                return "b1"
            end
        else
            if extra == 2 then
                return "b2"
            end
        end
    end
    if tag == "c" and flag then
        for i = 1, #items do
            if items[i] == extra then
                return "c:" .. i
            end
        end
        if extra == 9 then
            return "c9"
        end
    end
    if tag == "d" and flag then
        if extra == 1 then
            return "d1"
        end
    end
    if tag == "e" and flag then
        if extra == 1 then
            return "e1"
        end
    end
    if tag == "f" and flag then
        if extra == 1 then
            return "f1"
        end
    end
    return "fallback:" .. tostring(tag)
end

local function flat_events(ev, code)
    if ev == "E1" then
        if code == 1 then
            return "e1-1"
        elseif code == 2 then
            return "e1-2"
        end
        return "e1-other"
    end
    if ev == "E2" then
        if code > 0 then
            return "e2-pos"
        end
        return "e2-nonpos"
    end
    if ev == "E3" then
        if code == 0 then
            return "e3-zero"
        end
        return "e3-nz"
    end
    return "unknown"
end

assert(dispatch_stages("a", true, 1, {}) == "a1")
assert(dispatch_stages("a", true, 2, {}) == "a2")
assert(dispatch_stages("a", true, 3, {}) == "fallback:a")
assert(dispatch_stages("b", true, 1, {}) == "b1")
assert(dispatch_stages("b", true, 3, {}) == "fallback:b")
assert(dispatch_stages("c", true, 7, { 3, 7, 9 }) == "c:2")
assert(dispatch_stages("c", true, 9, { 1, 2 }) == "c9")
assert(dispatch_stages("c", true, 4, { 1, 2 }) == "fallback:c")
assert(dispatch_stages("d", true, 1, {}) == "d1")
assert(dispatch_stages("e", true, 1, {}) == "e1")
assert(dispatch_stages("f", true, 1, {}) == "f1")
assert(dispatch_stages("z", false, 0, {}) == "fallback:z")

assert(flat_events("E1", 1) == "e1-1")
assert(flat_events("E1", 2) == "e1-2")
assert(flat_events("E1", 9) == "e1-other")
assert(flat_events("E2", 5) == "e2-pos")
assert(flat_events("E2", 0) == "e2-nonpos")
assert(flat_events("E3", 0) == "e3-zero")
assert(flat_events("E3", 4) == "e3-nz")
assert(flat_events("E9", 0) == "unknown")
print("branch_40_sequential_early_return_merge", "OK")
