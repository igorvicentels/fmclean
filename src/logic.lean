section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intros p not_p,
  exact not_p(p),
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro not_not_p,
  by_contra not_p,
  exact not_not_p(not_p),
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  exact doubleneg_elim P,

  exact doubleneg_intro P,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro p_or_q,
  cases p_or_q with p q,
  right,
  exact p,
  left,
  exact q,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro p_and_q,
  cases p_and_q with p q,
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
  intros neg_p_or_q p,
  cases neg_p_or_q with neg_p q,
  exfalso,
  exact neg_p(p),

  exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intros p_or_q not_p,
  cases p_or_q with p q,
  exfalso,
  exact not_p(p),

  exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros p_imp_q not_q,
  intro p,
  have q := p_imp_q(p),
  exact not_q(q),
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros not_q_imp_not_p p,
  by_contra not_q,
  have not_p := not_q_imp_not_p(not_q),
  exact not_p(p),
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  exact impl_as_contrapositive P Q,

  exact impl_as_contrapositive_converse P Q,
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
  intro h2,
  have p_or_not_p : (P ∨ ¬P),
  left,
  exact h2,

  exact h1 p_or_not_p,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro h1,
  intro not_p,
  apply not_p,
  apply h1,
  intro p,
  exfalso,
  exact not_p p, 
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro p_or_q,
  intro h1,
  cases h1 with not_p not_q,
  cases p_or_q with p q,
  exact not_p p,

  exact not_q q,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro p_and_q,
  intro h1,
  cases p_and_q with p q,
  cases h1 with not_p not_q,
  exact not_p p,

  exact not_q q,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_ndisj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro h,
  split,
  intro p,
  apply h,
  left,
  exact p,

  intro q,
  apply h,
  right,
  exact q,
end

theorem demorgan_ndisj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro not_p_and_not_q,
  intro p_or_q,
  cases not_p_and_not_q with not_p not_q,
  cases p_or_q with p q,
  exact not_p p,
  exact not_q q,
end

theorem demorgan_nconj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro not_q_or_not_p,
  intro p_or_q,
  cases not_q_or_not_p with not_q not_p,
  cases p_or_q with p q,
  exact not_q q,
  
  cases p_or_q with p q,
  exact not_p p,
end


------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro h,
  cases h with p q_or_r,
  cases q_or_r with q r,
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
  intro h,
  cases h with p_and_q p_and_r,
  cases p_and_q with p q,
  split,
  exact p,
  
  left,
  exact q,
  
  cases p_and_r with p r,
  split,
  exact p,
  
  right,
  exact r,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h,
  split,
  cases h with p q_and_r,
  left,
  exact p,

  cases q_and_r with q r,
  right,
  exact q,

  cases h with p q_and_r,
  left,
  exact p,

  cases q_and_r with q r,
  right,
  exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h,
  cases h with p_or_q p_or_r,
  cases p_or_r with p r,
  left,
  exact p,

  cases p_or_q with p q,
  left,
  exact p,

  right,
  split,
  exact q,
  exact r,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros h p q,
  apply h,
  split,
  exact p,
  exact q,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros h p_and_q,
  apply h,
  exact p_and_q.left,

  exact p_and_q.right,
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
  intro p_and_q,
  exact p_and_q.left,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro p_and_q,
  exact p_and_q.right,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro p_and_p,
  exact p_and_p.left,

  intro p,
  split,
  exact p,
  exact p,

end

theorem disj_idemp :
  (P∨P) ↔ P  :=
begin
  split,
  intro p_or_p,
  cases p_or_p with p p,
  exact p,

  exact p,

  intro p,
  left,
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
  intro h,
  intro f,
  cases h with u hu,
  have p_u := f u,
  exact hu p_u,
end

theorem demorgan_neg_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro h,
  intro u,
  intro p_u,
  apply h,
  existsi u,
  exact p_u,
end

theorem demorgan_forall_neg :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro h1,
  intro h2,
  cases h2 with u hu,
  exact h1 u hu,
end

theorem demorgan_neg_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro h,
  by_contradiction hboom,
  apply h,
  intro u,
  by_contradiction hboom2,
  apply hboom,
  existsi u,
  exact hboom2,
end

theorem demorgan_exists_law :
  (∃x, ¬P x) ↔ ¬(∀x, P x)  :=
begin
  sorry,
end

theorem demorgan_forall_law :
  (∀x, ¬P x) ↔ ¬(∃x, P x)  :=
begin
  sorry,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  sorry,
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
  sorry,
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
