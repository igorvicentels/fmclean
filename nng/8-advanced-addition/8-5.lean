intro h,
induction t with d hd,
repeat{rw add_zero at h},
rw h,
refl,

repeat{rw add_succ at h},
have f := succ_inj h,
exact hd(f),