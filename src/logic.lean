section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
   intro p, -- chamando um novo p --
   intro q, --chamando um q que será meu -p --
   apply q, -- Opa! agora ele se converteu para p --
   exact p, -- Aqui está, se -p então p que é --p --
  
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro h1,
  by_cases p : P, -- pegando P e partindo em dois positivo e negativo
  exact p,
  contradiction, -- Opa! temos uma contradição :p
  
  
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  exact doubleneg_elim P, --Pegamos o caso --P -> P ALVO(P -> --P) --
  exact doubleneg_intro P,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=

begin
  intro pq, -- Ganhamos P V Q como dado, nosso alvo é Q V P --
  cases pq with hp hq, --Separamos em dois --
  right, -- chame a da direita --
  exact hp, -- Portanto é hp --
  left, -- chame a da esquerca --
  exact hq, -- retorne que é hq -- 

end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro pq,
  cases pq with p q,
  split,
  exact q,
  exact p,
  
  

end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro h1,
  intro h2,
  cases h1 with p q,
  contradiction,
  exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro h1,
  intro h2,
  cases h1 with p q,
  contradiction,
  exact q,


end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros h1 h2 h3,
  have h4 := h1 h3,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro h1,
  intro h_p,
  by_cases h_q : Q, --Caso sim e caso não
  exact h_q,
  exfalso,
  have new_q := h1 h_q, --Opa! -q e -p estão no mesmo barco
  contradiction,


end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  apply impl_as_contrapositive,
  apply impl_as_contrapositive_converse,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro h1,
  apply h1,
  right,
  intro p,
  have h1p : P ∨ ¬P,
  left,
  exact p,
  contradiction,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros h1 h2,
  have h1 : P,
  apply h1,
  intro p,
  exfalso,
  contradiction,
  contradiction,
  
  
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros h1 h2,
  cases h2 with h_p h_q,
  cases h1,
  contradiction,
  contradiction,
  
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros h1 h2,
  cases h2 with p q,
  cases h1,
  contradiction,
  cases h1 with p q,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_ndisj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro h1,
  split,
  intro h_p,
  have h1 : P ∨ Q,
  left,
  exact h_p,
  contradiction,
  intro h_q,
  have h1 : P ∨ Q,
  right,
  exact h_q,
  contradiction,
  
end

theorem demorgan_ndisj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros h1 h2,
  cases h1 with p q,
  cases h2 with pp qq,
  contradiction,
  contradiction,
end

theorem demorgan_nconj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro h1,
  intro h2,
  cases h1 with h_np h_nq,
  cases h2 with p q,
  contradiction,
  cases h2 with p q,
  contradiction,
  
end


------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro h,
  cases h with p h2,
  cases h2 with q r,
  left,
  split,
  exact p,
  exact q,
  right,
  split,
  exact p,
  exact r,
  
  

end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro h1,
  split,
  cases h1 with p_q p_r,
  cases p_q with p q,
  exact p,
  cases p_r with p r,
  exact p,
  cases h1 with p_q p_r,
  cases p_q with p q,
  left,
  exact q,
  right,
  cases p_r with p r,
  exact r,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h1,
  split,
  cases h1 with h_p h_qr,
  left,
  exact h_p,
  cases h_qr with q r,
  right,
  exact q,
  cases h1 with h_p h_qr,
  left,
  exact h_p,
  cc,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h1,
  cases h1 with h_pq h_pr,
  cases h_pr with p qr,
  left,
  exact p,
  cases h_pq with p q,
  left,
  exact p,
  right,
  split,
  exact q,
  exact qr,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro h1,
  intro h2_p,
  intro h3_q,
  apply h1,
  split,
  exact h2_p,
  exact h3_q,
  
  
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro h1,
  intro h_pq,
  apply h1,
  cases h_pq with p q,
  exact p,
  cases h_pq with p q,
  exact q,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p, 
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pq,
  cases pq with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,
  cases pq with  p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro pp1,
  cases pp1 with p1 p2,
  exact p1,
  intro pp2,
  split,
  repeat {exact pp2},
  
end

theorem disj_idemp :
  (P∨P) ↔ P  :=
begin
  split,
  intro pp1,
  cases pp1 with p1 p2,
  exact p1,
  exact p2,
  intro p,
  right,
  exact p,


end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists_neg :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro exits,
  cases exits with x h_not_P,
  intro all,
  apply h_not_P,
  have Pu: P x := all x,--no fim
  --Olha eu tenho P x no para todo x e ele será minha hipotese Pu
  exact Pu,
end

theorem demorgan_neg_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro exits,
  intro u,
  intro pb,
  apply exits, --Ficou falso então... o que na nossa prop é falso tbm :p
  existsi u,
  exact pb,

end

theorem demorgan_forall_neg :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro all,
  intro exist,
  cases exist with x exist_x, 
  have hneg := all  x, --pegue o -p no all (ai sera minha hipotese hneg)
  contradiction, -- :p
  
  
end

theorem demorgan_neg_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
 intro all,
 by_contra ne,
 apply all, --blz peguei o all sem neg,
 intro u,
 by_contra no_u,
 apply ne, --hehehe peguei o exist
 existsi u,
 intro prop_u,
 apply no_u,
 exact prop_u,

end

theorem demorgan_exists_law :
  (∃x, ¬P x) ↔ ¬(∀x, P x)  :=
begin
  split,
  apply demorgan_exists_neg,
  apply demorgan_neg_forall,
end

theorem demorgan_forall_law :
  (∀x, ¬P x) ↔ ¬(∃x, P x)  :=
begin
  split,
  apply demorgan_forall_neg,
  apply demorgan_neg_exists,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro exist,
  intro all,
  cases exist with x,
  apply all,
  have npx := all x,
  contradiction,
  exact x,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro x,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
  sorry,
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
  sorry,
end

---------------------------------------------- -/

end predicate
