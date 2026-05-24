-- regress_08_goto_loop_phi_seed#1: goto 进入 phi label 时入口初值不能被回边快照覆盖
-- unluac: expect-not-contains [[r0_1 = r0_0]]
-- unluac: expect-not-contains [[r0_2 = r0_1]]
-- unluac: expect-not-contains [[r0_0 = r0_1 + 1]]
-- unluac: expect-not-contains [[r0_1 = r0_2 + 1]]
while true do
    local i = 0
    goto L
    ::L2::
    print("regress_08_goto_loop_phi_seed#1", 2)
    ::L::
    print("regress_08_goto_loop_phi_seed#1", 1)
    i = i + 1
    if i == 1 then
        goto L2
    end
    break
end