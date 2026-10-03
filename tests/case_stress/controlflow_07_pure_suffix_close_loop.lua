-- 同槽纯链位于作用域回边区域；前缀副本不属于末端赋值的依赖闭包。
-- unluac: expect-ast-min [[while]] [[1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
-- 保留真实寄存器/作用域形状，验证相邻后缀能共享 DAG 展开且不改变循环入口。
local function run(a, done)
 ::again::
 do
  local reset0=0
  local reset1=0
  local reset2=0
  local reset3=0
  local reset4=0
  local reset5=0
  local reset6=0
  local reset7=0
 end
 if done then return end
 do
  local copy0=a
  local copy1=a
  local copy2=a
  local copy3=a
  local copy4=a
  local copy5=a
  local copy6=a
  local copy7=a
  done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done
  done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done
  done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done
  done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done
  done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done
  done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done
  done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done
  done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done
  done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done
  done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done
  done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done
  done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done
  done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done
  done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done
  done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done
  done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done; done=not done
  a.x=done
  done=true
  goto again
 end
end
local writes = 0
local a = setmetatable({}, {__newindex = function(owner, key, value)
    writes = writes + 1
    assert(key == "x" and value == false)
    assert(debug.setlocal(2, 1, nil) ~= nil)
    -- 回调期间八个原 COPY 都必须仍在其槽中，不能被额外 holder 改变前缀。
    for slot = 3, 10 do
        local name, snapshot = debug.getlocal(2, slot)
        assert(name ~= nil and snapshot == owner)
    end
    rawset(owner, key, value)
end})
run(a,false)
assert(a.x==false and writes==1)
run(a,true)
assert(writes==1)
print("regress_549_pure_suffix_close_loop", "OK")
