induction t with d hd,
repeat{rw zero_add},
exact h,

cases hd with k hk,
use k,
repeat{rw succ_add},
rw hk,
refl,