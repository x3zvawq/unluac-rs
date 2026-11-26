local sum = 0
-- unluac: expect-ast-count [[method-call]] [[16]]
local function mark(value)
    sum = sum + value
    return value
end
local function make()
    return function(value)
        assert(value > 0)
        return make()
    end
end
local function new_object()
    local object = { total = 0 }
    function object:next(value)
        self.total = self.total + value
        return self
    end
    return object
end
local fn = make()
fn = fn(mark(1))
fn = fn(mark(2))
fn = fn(mark(3))
fn = fn(mark(4))
fn = fn(mark(5))
fn = fn(mark(6))
fn = fn(mark(7))
fn = fn(mark(8))
fn = fn(mark(9))
fn = fn(mark(10))
fn = fn(mark(11))
fn = fn(mark(12))
fn = fn(mark(13))
fn = fn(mark(14))
fn = fn(mark(15))
fn = fn(mark(16))
assert(type(fn) == "function")
local object = new_object()
object = object:next(mark(1))
object = object:next(mark(2))
object = object:next(mark(3))
object = object:next(mark(4))
object = object:next(mark(5))
object = object:next(mark(6))
object = object:next(mark(7))
object = object:next(mark(8))
object = object:next(mark(9))
object = object:next(mark(10))
object = object:next(mark(11))
object = object:next(mark(12))
object = object:next(mark(13))
object = object:next(mark(14))
object = object:next(mark(15))
object = object:next(mark(16))
assert(object.total == 136)
assert(sum == 272)
print("self-call-updates", "OK")
