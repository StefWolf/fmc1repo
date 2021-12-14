cases b with d,
refl,
rw add_succ at H,
exfalso, --Vamos dizer que succ(d) + 0 = 0 é falso
have h1 := succ_ne_zero (a+d), --Nossa primeira hipótese sendo "diferente"
have h2 := h1(H), --Agora colocados nossa hipotese primeiro na antiga hipotese e agora ela é a segunda hipotese.
exact h2, --Olha só! ela é falsa mesmo :p