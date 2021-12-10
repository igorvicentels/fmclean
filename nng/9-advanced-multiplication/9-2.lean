cases a with h,
rw zero_mul at h,
left,
exact h,

rw succ_mul at h,
have h1 := add_left_eq_zero h,
right,
exact h1,