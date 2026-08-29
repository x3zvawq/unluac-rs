-- unluac: expect-not-contains [[1 == 1.0]]
-- unluac: expect-not-contains [[1 < 1.5]]
-- unluac: expect-contains [[return true, true, false]]

return 1 == 1.0, 1 < 1.5, 1.5 <= 1
