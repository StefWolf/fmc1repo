intro pq_qp, --pq
cases pq_qp with one two, --qr pr
intro qr, --qr
cases qr with q r,
split,
intro p,
apply q,
apply one,
exact p,
intro r_two,
apply two,
apply r,
exact r_two,