induction n with d hd,
rw mul_zero,
repeat{rw pow_zero},

rw mul_succ,
rw pow_succ,
rw hd,
rw pow_add,
refl,