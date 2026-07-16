local function wide_boolean_chain(
    a01, a02, a03, a04, a05, a06, a07, a08, a09, a10,
    a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
    a21, a22, a23, a24, a25, a26, a27, a28, a29, a30,
    a31, a32, a33, a34, a35, a36, a37, a38, a39, a40,
    a41, a42, a43, a44, a45, a46, a47, a48, a49, a50,
    a51, a52, a53, a54, a55, a56, a57, a58, a59, a60,
    a61, a62, a63, a64, a65, a66, a67, a68, a69, a70,
    a71, a72, a73, a74, a75, a76, a77, a78, a79, a80
)
    return (a01 and a02) or (a03 and a04) or (a05 and a06) or (a07 and a08)
        or (a09 and a10) or (a11 and a12) or (a13 and a14) or (a15 and a16)
        or (a17 and a18) or (a19 and a20) or (a21 and a22) or (a23 and a24)
        or (a25 and a26) or (a27 and a28) or (a29 and a30) or (a31 and a32)
        or (a33 and a34) or (a35 and a36) or (a37 and a38) or (a39 and a40)
        or (a41 and a42) or (a43 and a44) or (a45 and a46) or (a47 and a48)
        or (a49 and a50) or (a51 and a52) or (a53 and a54) or (a55 and a56)
        or (a57 and a58) or (a59 and a60) or (a61 and a62) or (a63 and a64)
        or (a65 and a66) or (a67 and a68) or (a69 and a70) or (a71 and a72)
        or (a73 and a74) or (a75 and a76) or (a77 and a78) or (a79 and a80)
end

return wide_boolean_chain(
    false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, true
)
