-- regress_316_large_ssa_scope_identity: SSA 定义多不等于源码 local 压力，不能因物理槽复用合并不同作用域身份
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[local r1_2 = 0.5]]
-- unluac: expect-not-contains [[    r1_2 = 0.5]]
-- unluac: expect-contains [[p1_0.worker:touch(1, 2, 3, 4)]]
-- unluac: expect-not-contains [[ = p1_0.worker]]
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[method-call]] [[62]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[3]] [[@proto=1]]

local function configure(subject)
    local width, height = 122, 165
    subject.width = width
    subject.height = height
    subject:record("size", width + height)

    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)
    subject.worker:touch(1, 2, 3, 4)

    local ratio = 0.5
    subject.ratio = ratio
    subject:record("ratio", ratio)
end

local subject = {
    total = 0,
    records = {}
}

function subject:touch(a, b, c, d)
    assert(a == 1 and b == 2 and c == 3 and d == 4)
    assert(self.width == 122 and self.height == 165 and self.ratio == nil)
    self.total = self.total + a + b + c + d
end

function subject:record(name, value)
    assert((name == "size" and self.total == 0) or (name == "ratio" and self.total == 600))
    self.records[#self.records + 1] = name .. ":" .. value
end

subject.worker = subject
configure(subject)
assert(subject.total == 600)
assert(subject.width == 122 and subject.height == 165 and subject.ratio == 0.5)
assert(table.concat(subject.records, ",") == "size:287,ratio:0.5")
print("regress_316_large_ssa_scope_identity", "OK")
