intro h,
induction a with d hd,
have h1 := le_zero (succ 0),
have h2 := h1 h,
have h3 := succ_ne_zero 0,
contradiction,

have h4 := le_of_succ_le_succ (succ d) d,
exact hd (h4 h),
