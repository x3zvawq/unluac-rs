-- Grids qualify for every small primitive kind: numbers, strings, booleans,
-- nil and plain names (no other literal shapes). Under the auto default only
-- numbers right-align; booleans and names left-align like strings, so this
-- file pins the left direction for the remaining primitive kinds.
-- unluac: expect-contains [[    true,  false, true,  false, true,  false, true,  false, true,  false,]]
-- unluac: expect-contains [[    alpha, beta,  gamma, alpha, beta,  gamma, alpha, beta,  gamma, alpha, beta,  gamma,]]
-- unluac: expect-not-contains [[     true, false,]]
local flags = {true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false}
local modes = {alpha, beta, gamma, alpha, beta, gamma, alpha, beta, gamma, alpha, beta, gamma, alpha, beta, gamma, alpha, beta, gamma, alpha, beta, gamma, alpha, beta, gamma}
print(flags[1], flags[#flags], modes[1], modes[#modes])
