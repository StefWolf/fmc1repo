split,
-- a * b = 0 --
apply eq_zero_or_eq_zero_of_mul_eq_zero,
intro h1,
cases h1, -- divide o left e right
rw h1,
rw zero_mul,
refl,
rw h1,
rw mul_zero,
refl,