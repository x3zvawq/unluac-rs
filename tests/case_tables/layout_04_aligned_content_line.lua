-- aligned style cascade, second step: a table that no longer fits flat on its
-- own line first tries to keep the whole constructor content on one indented
-- line between the braces before falling back to one entry per line or a grid.
-- unluac: expect-not-contains [[theta = 8 }]]
-- unluac: expect-contains [[    alpha = 1, beta = 2, gamma = 3, delta = 4, epsilon = 5, zeta = 6, eta = 7, theta = 8]]
local fallback = {alpha = 1, beta = 2, gamma = 3, delta = 4, epsilon = 5, zeta = 6, eta = 7, theta = 8}
print(fallback.alpha, fallback.theta)
