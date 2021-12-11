repeat {rw not_iff_imp_false},
intro pq,
intro qf,
intro pf,
apply qf, -- troca false por Q --
apply pq,
exact pf,
