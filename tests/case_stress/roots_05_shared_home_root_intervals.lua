-- 多个独立物理根共享长运算后缀，跨回边后分别在原 home 的常量覆盖处退休。
local function run(a, done)
 local copy0
 local copy1
 local copy2
 local copy3
 local copy4
 local copy5
 local copy6
 local copy7
 local copy8
 local copy9
 local copy10
 local copy11
 local copy12
 local copy13
 local copy14
 local copy15
 ::again::
 copy0=0
 copy1=0
 copy2=0
 copy3=0
 copy4=0
 copy5=0
 copy6=0
 copy7=0
 copy8=0
 copy9=0
 copy10=0
 copy11=0
 copy12=0
 copy13=0
 copy14=0
 copy15=0
 if done then return end
 copy0=a
 copy1=a
 copy2=a
 copy3=a
 copy4=a
 copy5=a
 copy6=a
 copy7=a
 copy8=a
 copy9=a
 copy10=a
 copy11=a
 copy12=a
 copy13=a
 copy14=a
 copy15=a
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 done=not done
 a.x=done
 done=true
 goto again
end
local a={}
run(a,false)
assert(a.x==false, "root interval changed loop write")
a.x=nil
run(a,true)
assert(a.x==nil, "initial exit executed loop body")
print("regress_546_shared_home_root_intervals", "OK")
