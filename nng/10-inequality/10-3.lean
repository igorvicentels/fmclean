intro h,
rw le_iff_exists_add at h ⊢,
cases h with c hc,
use succ(c),
rw add_succ,
rw hc,
refl,