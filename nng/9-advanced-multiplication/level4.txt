induction c with d hd generalizing b,

-- Base
intro h,
rw mul_zero at h,
have a_zero_or_b_zero := eq_zero_or_eq_zero_of_mul_eq_zero a b h,
cases a_zero_or_b_zero with a_zero  b_zero,
contradiction,
exact b_zero,

-- Passo indutivo
intro h,
cases b with b',
  -- Caso b = 0
  rw mul_zero at h,
  symmetry at h,
  have a_zero_or_succ_d_zero := eq_zero_or_eq_zero_of_mul_eq_zero a _ h,
  cases a_zero_or_succ_d_zero with a_zero succ_d_zero,
  contradiction,
  symmetry at succ_d_zero,
  exact succ_d_zero,
  
  -- Caso b = Sb'
  repeat{rw mul_succ at h},
  have ab'_eq_ad := add_right_cancel (a * b') a (a * d) h,
  have hd1 := hd b',
  have a_eq_b := hd1 ab'_eq_ad,
  rw a_eq_b,
  refl,