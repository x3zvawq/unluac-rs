local weak = setmetatable({}, {__mode="v"})
local nextkey=1
local function pair()
  local a,b={},{}
  weak[nextkey],weak[nextkey+1]=a,b
  nextkey=nextkey+2
  return a,b
end
local function run()
  do
    local a,b=pair()
    collectgarbage("collect")
    assert(weak[1]~=nil and weak[2]~=nil)
  end
  do
    local a,b=pair()
    a,b=nil,nil
    collectgarbage("collect")
    assert(weak[3]==nil and weak[4]==nil)
  end
end
run()
print("grouped-owner-chain", "OK")
