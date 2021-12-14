intros h1 h2 h3,
cases b with n,
rw mul_zero at h3,
have h4 := h2(h3),
exact h4,
rw mul_succ a n at h3, --escolho demonstrar o h3
have h4 := add_left_eq_zero(h3),
exact h1(h4), -- h1 mostra que são diferentes e h4 mostra que são iguais, então, falso né!?