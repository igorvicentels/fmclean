intros h f g,
cases b with d,
rw mul_zero at g,
exact f g,

rw mul_succ at g,
have g1 := add_left_eq_zero g,
exact h g1,