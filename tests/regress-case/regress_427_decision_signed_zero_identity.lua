local function preserve_positive_zero(x)
    local subject = x and 0.0
    if subject then
        return (x == 0.0) and 0.0
    end
    return x
end

print(
    "regress_427_decision_signed_zero_identity",
    1 / preserve_positive_zero(-0.0)
)
