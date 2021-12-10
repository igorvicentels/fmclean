induction c with d hd,
repeat{rw mul_zero},

repeat{rw mul_succ},
repeat{rw mul_add},
rw hd,
rw mul_comm a b,
refl,
