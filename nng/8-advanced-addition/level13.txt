induction n with d hd,
intro h,
have f := zero_ne_succ 0,
exact f h,

intro h,
have f := succ_inj h,
exact hd f,