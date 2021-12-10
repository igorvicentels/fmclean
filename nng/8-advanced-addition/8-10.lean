cases b with d,
refl,

rw add_succ at H,
have f := succ_ne_zero (a+d),
exfalso,
exact f(H),