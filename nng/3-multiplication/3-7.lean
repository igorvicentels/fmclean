induction t with d hd,
repeat{rw mul_zero},
rw add_zero,
refl,

repeat{rw mul_succ},
rw hd,
simp,