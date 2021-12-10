intro h,
induction a with d hd,
rw zero_add at h,
rw h,
refl,

rw succ_add at h,
have f := succ_inj h,
exact hd f,