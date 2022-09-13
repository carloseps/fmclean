
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intros h1 h2,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  by_cases hipo : P,
    intro h1,
    apply hipo,

    intro h1,
    have newhipo := h1 hipo,
    contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  have primeiraHipo := doubleneg_elim P,
    apply primeiraHipo,
  have segundaHipo := doubleneg_intro P,
    apply segundaHipo,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro h1,
  cases h1,
  right,
    apply h1,
  left,
    apply h1,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro h1,
  cases h1 with part1 part2,
  split,
  apply part2,
  apply part1,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intros h1 h2,
  cases h1,
  contradiction,
  apply h1,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intros h1 h2,
  cases h1,
  contradiction,
  apply h1,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros h1 h2 h3,
  have newhipo : Q := h1 h3,
    contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros h1 h2,
  by_cases q: Q,
    assumption,
    have newhipo := h1 q,
      contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  have primeiraHipo := impl_as_contrapositive P Q,
    apply primeiraHipo,
  have segundaHipo := impl_as_contrapositive_converse P Q,
    apply segundaHipo,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intros h1,
  have leiTercEscolh : P ∨ ¬P,
    right,
    intro h2,
    have leiTercEscolhOutraParte : P ∨ ¬P,
      left,
      apply h2,
      contradiction,
  contradiction,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros h1 h2,
  have newhipo : P → Q,
    intro h2,
    contradiction,
  have obterP := h1 newhipo,
    contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros h1 h2,
  cases h2 with hp hq,
  cases  h1,
    contradiction,
    contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros h1 h2,
  cases h1 with hp hq,
  cases h2,
    contradiction,
    contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro h1,
  split,
    intro hp,
    have newhipo : (P∨Q),
    left,
      apply hp,
      contradiction,
    intro hq,
    have newhipo : (P∨Q),
      right,
      apply hq,
      contradiction,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros h1 h2,
  cases h1 with naop naoq,
    cases h2,
    contradiction,
    contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro h1,
  by_cases P,
  left,
  by_contradiction q,
  have newhipo : P∧Q,
    split,
    repeat {assumption},
  contradiction,
  right,
  assumption,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros h1 h2,
  cases h2 with hp hq,
    cases h1 with naoq naop,
    contradiction,
    contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  have primeiraHipo := demorgan_conj P Q,
    apply primeiraHipo,
  have segundaHipo := demorgan_conj_converse P Q,
    apply segundaHipo,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  have primeiraHipo := demorgan_disj P Q,
    apply primeiraHipo,
  have segundaHipo := demorgan_disj_converse P Q,
    apply segundaHipo,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro h1,
  cases h1 with hp hqr,
  cases hqr,
  left,
    split,
      assumption,
      assumption,
  right,
    split,
      assumption,
      assumption,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro h1,
  split,
  cases h1,
    cases h1 with hq hpr,
    assumption,
      cases h1 with p q,
      assumption,
      cases h1,
        cases h1 with hp hq,
        left,
          assumption,
        cases h1 with hp hpr,
        right,
        assumption,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h1,
  cases h1,
    split,
    left,
      assumption,
      left,
        assumption,
    cases h1 with hq hr,
    split,
    right,
      assumption,
    right,
      assumption,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h1,
  cases h1 with pq pr,
  cases pq with p q,
    left,
      assumption,
    cases pr with p r,
      left,
        assumption,
      right,
        split,
          repeat {assumption},
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros h1 h2 h3,
  have newhipo : (P∧Q),
  split,
    assumption,
    assumption,
  apply h1 newhipo,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros h1 h2,
  cases h2 with hp hq,
  apply h1 hp hq,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro h1,
  assumption,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro h1,
  left, --escolhe lado esquerdo do alvo
  assumption,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro h1,
  right, --escolhe lado direito do alvo
  assumption,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro h1,
  cases h1 with hp hq,
    assumption,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro h1,
  cases h1 with hp hq,
    assumption,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro h1,
  cases h1,
    assumption,
  intro h2,
    split,
      assumption,
      assumption,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro h1,
  cases h1,
    assumption,
    assumption,
  intro h2,
    right, --ou esquerda, tanto faz
      assumption,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intros nEa a pA,
  apply nEa,
  existsi a,
  assumption,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intros pTdA eA,
  cases eA with a,
  have newhipo := pTdA a,
  contradiction,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intros eA pTdA,
  cases eA with a,
  have newhipo := pTdA a,
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intros eA nPtdA,
  cases eA with u pU,
  have newhipo := nPtdA u,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intros pTdA eA,
  cases eA with a nPa,
  have newhipo := pTdA a,
  contradiction,
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
  intro h1,
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
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
