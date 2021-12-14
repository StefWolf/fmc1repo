intro h1,
induction a with aa ha,
rw zero_add at h1, -- faça isso no h1
exact h1,
rw succ_add at h1,
apply ha,
apply succ_inj,
exact h1, -- temos esse dado