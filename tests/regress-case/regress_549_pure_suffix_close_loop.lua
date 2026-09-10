-- 同槽纯链位于带 Close 的回边区域；前缀副本不属于末端赋值的依赖闭包。
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
local a={}
run(a,false)
assert(a.x==false)
print("regress_549_pure_suffix_close_loop", "OK")
