induction a with d hd,
rw zero_add,
rw mul_zero,
rw zero_add,
refl,

rw succ_add,
rw mul_succ,
rw hd,
rw mul_succ,
rw add_comm _ t,
rw add_comm _ t,
rw add_assoc,
refl,