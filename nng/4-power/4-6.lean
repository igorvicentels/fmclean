induction n with d hd,
repeat{rw pow_zero},
rw mul_one,
refl,

repeat{rw pow_succ},
rw hd,
simp,