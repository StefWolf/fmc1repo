split,
intro p_q_r,
cases p_q_r with p q_r,
cases q_r with q r,
left, --esq
split, --divid
exact p, --isso aqui
exact q, --isso aqui
right, --dir
split, --divid
exact p, --isso aqui
exact r, --isso aqui
intro p_qvp_r, --crie h
cases p_qvp_r with p_e_q p_e_r, --divide o h em dois
cases p_e_q with p q, --divide o a em dois
split, --divide
exact p, --isso aqui
left, --esquerda
exact q, --isso aqui
cases p_e_r with p r, --divide em dois
split, --divide
exact p, --isso aqui
right, --direita
exact r, --isso aqui