intro succa_le_succb,
induction a with d hd,
exact zero_le b,

cases succ(d) with d',
exact zero_le b,

cases succa_le_succb with k hk,
rw succ_add at hk,

have b_eq_succ_d'_k := succ_inj hk,
use k,
rw b_eq_succ_d'_k,
refl,
