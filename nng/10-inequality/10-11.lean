intro a_le_b,
intro t,

induction t with d hd,
repeat{rw add_zero},
exact a_le_b,

cases a_le_b with k hb,
cases hd with l hl,
use l,
rw add_succ,
rw add_succ,
rw hl,
rw succ_add,
refl,