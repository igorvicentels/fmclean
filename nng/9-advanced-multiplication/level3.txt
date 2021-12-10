split,
exact eq_zero_or_eq_zero_of_mul_eq_zero a b,

intro h,
cases h,
rw h,
rw zero_mul,
refl,

rw h,
rw mul_zero,
refl,