induction n with nn hn,
rw pow_zero,
rw pow_zero,
rw pow_zero,
refl,
repeat {rw pow_succ},
rw hn,
simp,