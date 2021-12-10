induction c with d hd,
repeat{rw mul_zero},

repeat{rw mul_succ},
rw hd,
rw mul_add,
refl,